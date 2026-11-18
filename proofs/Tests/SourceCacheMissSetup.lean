import SubtreeProofs.Rust.SourcePairTailEntry
import SubtreeProofs.Rust.SourcePairTailScopeEntry
import SubtreeProofs.Rust.SourcePairScoreEntry

namespace SourceCacheMissSetupTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

-- Both empty queries borrow the same inline word in a Box owned by the input
-- table. The table's right key is nonempty, so independent lookup must miss.
private def table : MemoTable := .Entry ⟨.Empty, .Pair .Empty .Empty, ⟨.Empty, 0#u32⟩⟩ .Empty
private def entry : Cell := .node .entry 0
  [.node .word 0 [], .node .word 1 [.owned 2, .owned 3],
   .node .embedding 0 [.node .word 0 [], .number 0]]
private def world : World := ⟨[entry, .node .table 0 [], .node .word 0 [], .node .word 0 []],
  fun address => if address < 4 then some .box else none, fun address => decide (address < 4)⟩
private def tableCell : Cell := .node .table 1 [.owned 0, .owned 1]
private def queryCell : Cell := .shared ⟨0, [0]⟩
private def packets : List ValueCell := SourceEval.Evaluator.inputPackets queryCell queryCell tableCell .Empty .Empty table

private theorem entry_graph : Graph world.memory entry
    (.node .entry 0 [encodeWord .Empty, encodeWord (.Pair .Empty .Empty), encodeResult ⟨.Empty, 0#u32⟩]) [2, 3] := by
  have result : Graph world.memory (.node .embedding 0 [.node .word 0 [], .number 0])
      (encodeResult ⟨.Empty, 0#u32⟩) [] := .node (.cons (.node .nil) (.cons (.number 0) .nil))
  exact .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl (.node .nil))
    (.cons (.owned rfl (.node .nil)) .nil))) (.cons result .nil)))

private theorem entry_footprint : Footprint world.memory entry [2, 3] := by
  have result : Footprint world.memory (.node .embedding 0 [.node .word 0 [], .number 0]) [] :=
    .node (.cons (.node .nil) (.cons (.number 0) .nil))
  exact .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl (.node .nil))
    (.cons (.owned rfl (.node .nil)) .nil))) (.cons result .nil)))

private theorem query_readable : Readable world.memory world.live queryCell (.reference (encodeWord .Empty)) :=
  ⟨[0], .shared rfl (.node .nil), by simp [AliveOn, world]⟩

private theorem table_readable : Readable world.memory world.live tableCell (encodeTable table) := by
  refine ⟨[2, 3, 0, 1], .node (.cons (.owned rfl entry_graph) (.cons (.owned rfl (.node .nil)) .nil)), ?_⟩
  simp [AliveOn, world]

private theorem resources : FieldsFootprint world.memory (packets.map Prod.fst) [2, 3, 0, 1] ∧
    OwnerFrame world ([2, 3, 0, 1] ++ (callerOwners world [] ++ [])) ∧
    BoxCoverage world ([2, 3, 0, 1] ++ (callerOwners world [] ++ [])) := by
  refine ⟨?_, ?_, ?_⟩
  · have owned : Footprint world.memory tableCell [2, 3, 0, 1] :=
      .node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))
    exact .cons (.shared _) (.cons (.shared _) (.cons owned .nil))
  · refine ⟨by decide +kernel, ?_, ?_⟩
    · intro address member
      have cases : address = 2 ∨ address = 3 ∨ address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
    · intro address member
      have cases : address = 2 ∨ address = 3 ∨ address = 0 ∨ address = 1 := by simpa [callerOwners] using member
      rcases cases with rfl | rfl | rfl | rfl <;> rfl
  · intro address classified _
    have bound : address < 4 := by simpa [world] using classified
    have cases : address = 2 ∨ address = 3 ∨ address = 0 ∨ address = 1 := by omega
    simpa [callerOwners] using cases

example : ∃ entered active minFuel minBudget lookupWorld lookupActive final after,
    LoanSafeMachine world [] {} [] final after ∧
    SourceEval.Evaluator.MissScope active .Empty .Empty table final after ∧
    LoanOrigin final after 4 13 ∧ WordLoanState after.state ∧
    after.state 13 = SourceEval.Evaluator.queryTuple .Empty .Empty ∧
    Derived.scrutinee final after [] (.discriminant (.deref (.field (.local 13) none 0))) = some (.variant .word 0, after) ∧
    Derived.scrutinee final after [] (.discriminant (.deref (.field (.local 13) none 1))) = some (.variant .word 0, after) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix
        entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions
        lookupWorld lookupActive final after := by
  have owned := resources
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, final, after, _, _, machine, scope,
    _, tupleOrigin, _, words, _, left, right, stable⟩ :=
    SourceEval.Evaluator.entry_miss_setup_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty table queryCell queryCell tableCell query_readable query_readable table_readable
      owned.1 owned.2.1 owned.2.2 (by simp [table, MemoizedOrderedSolver.findResult])
  exact ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, final, after, machine, scope,
    tupleOrigin, words, scope.tuple, left, right, stable⟩

-- Complete invocation now includes native insertion, all cleanup, checked
-- closure and one fixed world/packet/full cost at every larger pair of bounds.
example : ∃ minFuel minBudget final packet lookupCost insertCost,
    packet.2 = SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness)
      (.Entry ⟨.Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ table) ∧
    Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
    (∃ output, Footprint final.memory packet.1 output ∧ OwnerFrame final output ∧ BoxCoverage final output) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Recursive.original budget fuel world [] [] .evaluate packets =
        some (final, packet, SourceEval.Evaluator.emptyRunCost .Empty lookupCost insertCost) := by
  have owned := resources
  obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, _, _, _, readable, wf, _, owners, stable⟩ :=
    SourceEval.Evaluator.empty_miss_total (guards := []) (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty table queryCell queryCell tableCell query_readable query_readable table_readable
      owned.1 owned.2.1 owned.2.2 (by simp) (Or.inl rfl) (by simp [table, MemoizedOrderedSolver.findResult])
  exact ⟨fuel, budget, final, packet, lookupCost, insertCost, value, readable, wf, by simpa [callerOwners] using owners, stable⟩

private def pairCell : Cell := .shared ⟨0, [1]⟩
private theorem pair_readable : Readable world.memory world.live pairCell (.reference (encodeWord (.Pair .Empty .Empty))) := by
  exact ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, world]⟩

-- The nonempty-left / empty-right route takes both actual word switches.
-- Both queries again read data owned by the table being transferred/inserted.
example : ∃ minFuel minBudget final packet lookupCost insertCost,
    packet.2 = SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness)
      (.Entry ⟨.Pair .Empty .Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ table) ∧
    Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
    (∃ output, Footprint final.memory packet.1 output ∧ OwnerFrame final output ∧ BoxCoverage final output) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Recursive.original budget fuel world [] [] .evaluate
        (SourceEval.Evaluator.inputPackets pairCell queryCell tableCell (.Pair .Empty .Empty) .Empty table) =
        some (final, packet, SourceEval.Evaluator.emptyRunCost (.Pair .Empty .Empty) lookupCost insertCost) := by
  have owned := resources
  have footprint : FieldsFootprint world.memory [pairCell, queryCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, _, _, _, readable, wf, _, owners, stable⟩ :=
    SourceEval.Evaluator.empty_miss_total (guards := []) (by simp [World.WellFormed, world]) (by simp) Callers.nil
      (.Pair .Empty .Empty) .Empty table pairCell queryCell tableCell pair_readable query_readable table_readable
      footprint owned.2.1 owned.2.2 (by simp) (Or.inr rfl) (by simp [table, MemoizedOrderedSolver.findResult])
  exact ⟨fuel, budget, final, packet, lookupCost, insertCost, value, readable, wf, by simpa [callerOwners] using owners, stable⟩

-- Both parent queries select the same nonempty word in the table-owned entry.
-- All four Box-field views overlap; the recursive head request is empty/empty.
-- Its contract is proved, so no successful-child-run premise is supplied.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive final after,
    OriginalLoanMachine world [] {} [] [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairHeadScope missActive .Empty .Empty .Empty .Empty (some SourceEval.Evaluator.emptyWitness)
      (.Entry ⟨.Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ table) final after ∧
    after.roots 33 = none ∧
    Derived.scrutinee final after [] (.discriminant (.local 31)) = some (.variant .optional 1, after) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix
        entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions
        lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions
        missWorld missActive final after := by
  have owned := resources
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, final, after, result, output,
    _, _, machine, scope, native, inspection, stable⟩ :=
    SourceEval.Evaluator.entry_pair_head_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table pairCell pairCell tableCell pair_readable pair_readable table_readable
      footprint owned.2.1 owned.2.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
  have expected := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans expected))
  exact ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, final, after,
    machine, scope, scope.retired 33 (by simp), inspection, stable⟩

private def headMemo : MemoTable := .Entry ⟨.Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ table

-- The head miss inserts Empty/Empty, and the actual tail recursion then hits
-- that updated table. Both recursive contracts are proved base instances;
-- no successful physical run or full pair/pair-totality premise is supplied.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    after.state 43 = Slot.ofValue (SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness) headMemo) ∧
    after.state 37 = Slot.ofValue (encodeResult SourceEval.Evaluator.emptyWitness) ∧
    after.state 31 = SourceEval.Evaluator.headPayloadHole ∧ after.state 32 = .empty ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix
        entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions
        lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions
        missWorld missActive headWorld headActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.tailCode 14) (SourceEval.Evaluator.tailActions.take 14)
        headWorld headActive final after := by
  have owned := resources
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    final, after, result, output, _, _, machine, value, payload, hole, emptyTable, native, stable⟩ :=
    SourceEval.Evaluator.entry_pair_tail_prefix_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo SourceEval.Evaluator.emptyWitness pairCell pairCell tableCell
      pair_readable pair_readable table_readable footprint owned.2.1 owned.2.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative
  have expected := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans expected))
  exact ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    final, after, machine, value, payload, hole, emptyTable, stable⟩

-- The complete tail prefix retires its argument/output roots and reaches the
-- actual result discriminant. Both original queries alias table-owned data;
-- both recursive contracts are discharged by proved native empty instances.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairTailScope headActive .Empty .Empty .Empty .Empty SourceEval.Evaluator.emptyWitness
      (some SourceEval.Evaluator.emptyWitness) headMemo final after ∧
    after.roots 43 = none ∧ after.roots 44 = none ∧ after.roots 45 = none ∧ after.roots 46 = none ∧
    Derived.scrutinee final after [] (.discriminant (.local 41)) = some (.variant .optional 1, after) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix
        entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions
        lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions
        missWorld missActive headWorld headActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions
        headWorld headActive final after := by
  have owned := resources
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    final, after, result, output, _, _, machine, scope, inspection, native, stable⟩ :=
    SourceEval.Evaluator.entry_pair_tail_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo SourceEval.Evaluator.emptyWitness pairCell pairCell tableCell
      pair_readable pair_readable table_readable footprint owned.2.1 owned.2.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative
  have expected := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans expected))
  exact ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    final, after, machine, scope, scope.retired 43 (by simp), scope.retired 44 (by simp),
    scope.retired 45 (by simp), scope.retired 46 (by simp), inspection, stable⟩


-- A head miss followed by a tail hit reaches the actual subtotal switch.
-- Both queries alias table-owned data; the witnesses stay owned while their
-- scalar arguments clear and retire. Only proved empty-input contracts are used.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.ScoreSumScope SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness headMemo final after ∧
    after.state 52 = Slot.ofValue (SourceEval.encodeNumberOption (some 0)) ∧
    after.roots 53 = none ∧ after.roots 54 = none ∧
    Derived.scrutinee final after [] (.discriminant (.local 52)) = some (.variant .optional 1, after) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix
        entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions
        lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions
        missWorld missActive headWorld headActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions
        headWorld headActive tailWorld tailActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions
        tailWorld tailActive final after := by
  have owned := resources
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, final, after, _, _, machine, scope, value, inspection, stable⟩ :=
    SourceEval.Evaluator.entry_pair_score_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      pairCell pairCell tableCell pair_readable pair_readable table_readable footprint owned.2.1 owned.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative
  refine ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, final, after, machine, scope, ?_, scope.retired 53 (by simp), scope.retired 54 (by simp), ?_, stable⟩
  · simpa [SourceEval.Evaluator.emptyWitness, SourceEval.checkedAdd32, SourceEval.checkedAdd32_native] using scope.result
  · simpa [SourceEval.Evaluator.emptyWitness, SourceEval.checkedAdd32, SourceEval.Evaluator.numberKey] using inspection


-- Arbitrary typed warm scores exercise the overflow branch without a cache
-- soundness premise. Both query references still point into the owned table.
private def maxWitness : CommonEmbedding := ⟨.Empty, 4294967295#u32⟩
private def maxEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 0 [], .number maxWitness.edges.val]]
private def overflowTable : MemoTable := .Entry ⟨.Empty, .Empty, maxWitness⟩ table
private def overflowCell : Cell := .node .table 1 [.owned 4, .owned 5]
private def overflowWorld : World := ⟨world.memory ++ [maxEntry, tableCell],
  fun address => if address < 6 then some .box else none, fun address => decide (address < 6)⟩

private theorem overflow_extends : Heap.Extends world.memory overflowWorld.memory := Heap.Extends.append _ _
private theorem max_graph : Graph overflowWorld.memory maxEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult maxWitness]) [] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons
    (.node (.cons (.node .nil) (.cons (.number _) .nil))) .nil)))
private theorem max_footprint : Footprint overflowWorld.memory maxEntry [] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons
    (.node (.cons (.node .nil) (.cons (.number _) .nil))) .nil)))
private theorem overflow_footprint : Footprint overflowWorld.memory overflowCell [4, 2, 3, 0, 1, 5] :=
  .node (.cons (.owned rfl max_footprint) (.cons (.owned rfl
    (.node (.cons (.owned rfl (Heap.Spatial.footprint_mono overflow_extends entry_footprint))
      (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
private theorem overflow_readable : Readable overflowWorld.memory overflowWorld.live overflowCell (encodeTable overflowTable) := by
  refine ⟨[4, 2, 3, 0, 1, 5], .node (.cons (.owned rfl max_graph) (.cons (.owned rfl
    (.node (.cons (.owned rfl (entry_graph.mono overflow_extends)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)), ?_⟩
  simp [AliveOn, overflowWorld]
private theorem overflow_pair_readable : Readable overflowWorld.memory overflowWorld.live pairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, overflowWorld]⟩
private theorem overflow_resources : OwnerFrame overflowWorld [4, 2, 3, 0, 1, 5] ∧
    BoxCoverage overflowWorld [4, 2, 3, 0, 1, 5] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 6 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [overflowWorld, bound]
  · intro address member
    have bound : address < 6 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [overflowWorld, bound]
  · intro address classified _
    have bound : address < 6 := by simpa [overflowWorld] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

example : ∃ final after,
    OriginalLoanMachine overflowWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.ScoreSumScope maxWitness maxWitness overflowTable final after ∧
    after.state 52 = Slot.ofValue (SourceEval.encodeNumberOption none) ∧
    Derived.scrutinee final after [] (.discriminant (.local 52)) = some (.variant .optional 0, after) := by
  have footprint : FieldsFootprint overflowWorld.memory [pairCell, pairCell, overflowCell] [4, 2, 3, 0, 1, 5] :=
    .cons (.shared _) (.cons (.shared _) (.cons overflow_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native overflowTable .Empty .Empty maxWitness
    (by simp [overflowTable, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, final, after,
    _, _, machine, scope, _, inspection, stable⟩ :=
    SourceEval.Evaluator.entry_pair_score_scope_complete (by simp [World.WellFormed, overflowWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty overflowTable overflowTable overflowTable maxWitness maxWitness pairCell pairCell overflowCell
      overflow_pair_readable overflow_pair_readable overflow_readable footprint
      (by simpa [callerOwners] using overflow_resources.1) (by simpa [callerOwners] using overflow_resources.2)
      (by simp [overflowTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit
  refine ⟨final, after, machine, scope, ?_, ?_⟩
  · simpa [maxWitness, SourceEval.checkedAdd32] using scope.result
  · simpa [maxWitness, SourceEval.checkedAdd32, SourceEval.Evaluator.numberKey] using inspection

end SourceCacheMissSetupTests
