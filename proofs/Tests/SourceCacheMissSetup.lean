import SubtreeProofs.Rust.SourcePairTailEntry
import SubtreeProofs.Rust.SourcePairTailScopeEntry
import SubtreeProofs.Rust.SourcePairScoreEntry
import SubtreeProofs.Rust.SourcePairRootScoreEntry
import SubtreeProofs.Rust.SourcePairMatchedEntry
import SubtreeProofs.Rust.SourcePairLeftConcatEntry
import SubtreeProofs.Rust.SourceContractionRequests
import SubtreeProofs.Rust.SourcePairLeftWordViewsEntry
import SubtreeProofs.Rust.SourceAnchorOwnerPermissions
import SubtreeProofs.Rust.SourcePairLeftCallEntry

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


-- All six actual prefix boundaries reach the root-score switch. Empty base
-- contracts discharge both recursive premises despite table-owned query aliases.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RootScoreScope SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness headMemo 0#u32 final after ∧
    after.state 59 = Slot.ofValue (SourceEval.encodeNumberOption (some 1)) ∧
    after.roots 52 = none ∧ after.roots 55 = none ∧ after.roots 60 = none ∧
    Derived.scrutinee final after [] (.discriminant (.local 59)) = some (.variant .optional 1, after) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions missWorld missActive headWorld headActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions headWorld headActive tailWorld tailActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions tailWorld tailActive scoreWorld scoreActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rootScoreCases SourceEval.Evaluator.rootScoreActions scoreWorld scoreActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, final, after,
    _, machine, scope, _, inspection, stable⟩ :=
    SourceEval.Evaluator.entry_pair_root_score_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel)
  refine ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, final, after, machine, scope,
    ?_, scope.retired 52 (by simp), scope.retired 55 (by simp), scope.retired 60 (by simp), ?_, stable⟩
  · simpa [SourceEval.checkedAdd32] using scope.result
  · simpa [SourceEval.checkedAdd32, SourceEval.Evaluator.numberKey] using inspection

private def rootOverflowWorld : World := ⟨overflowWorld.memory ++ [.node .word 0 [], .node .word 0 [], .node .word 0 [],
  .node .word 1 [.owned 7, .owned 8], .node .word 1 [.owned 6, .owned 9]],
  fun address => if address < 11 then some .box else none, fun address => decide (address < 11)⟩
private def largerPairCell : Cell := .shared ⟨10, []⟩
private theorem root_overflow_extends : Heap.Extends overflowWorld.memory rootOverflowWorld.memory := Heap.Extends.append _ _
private theorem root_overflow_table_readable : Readable rootOverflowWorld.memory rootOverflowWorld.live overflowCell (encodeTable overflowTable) := by
  obtain ⟨reads, graph, alive⟩ := overflow_readable
  refine ⟨reads, graph.mono root_overflow_extends, ?_⟩
  intro address member
  have bound : address < 6 := by simpa [overflowWorld] using alive address member
  simp [rootOverflowWorld]; omega
private theorem root_overflow_pair_readable : Readable rootOverflowWorld.memory rootOverflowWorld.live pairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, rootOverflowWorld]⟩
private theorem larger_pair_readable : Readable rootOverflowWorld.memory rootOverflowWorld.live largerPairCell
    (.reference (encodeWord (.Pair .Empty (.Pair .Empty .Empty)))) :=
  ⟨[6, 7, 8, 9, 10], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))),
    by simp [AliveOn, rootOverflowWorld]⟩
private theorem root_overflow_resources : OwnerFrame rootOverflowWorld ([4, 2, 3, 0, 1, 5] ++ (callerOwners rootOverflowWorld [] ++ [6, 7, 8, 9, 10])) ∧
    BoxCoverage rootOverflowWorld ([4, 2, 3, 0, 1, 5] ++ (callerOwners rootOverflowWorld [] ++ [6, 7, 8, 9, 10])) := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 11 := by simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [rootOverflowWorld, bound]
  · intro address member
    have bound : address < 11 := by simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [rootOverflowWorld, bound]
  · intro address classified _
    have bound : address < 11 := by simpa [rootOverflowWorld] using classified
    simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega

-- The two smaller requests hit different warm keys: max-width head score and
-- zero tail score. Their subtotal succeeds; adding the root edge alone overflows.
example : ∃ final after,
    OriginalLoanMachine rootOverflowWorld [] {} [6, 7, 8, 9, 10] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RootScoreScope maxWitness SourceEval.Evaluator.emptyWitness overflowTable 4294967295#u32 final after ∧
    after.state 59 = Slot.ofValue (SourceEval.encodeNumberOption none) ∧
    Derived.scrutinee final after [] (.discriminant (.local 59)) = some (.variant .optional 0, after) := by
  have footprint : FieldsFootprint rootOverflowWorld.memory [pairCell, largerPairCell, overflowCell] [4, 2, 3, 0, 1, 5] :=
    .cons (.shared _) (.cons (.shared _) (.cons (Heap.Spatial.footprint_mono root_overflow_extends overflow_footprint) .nil))
  have headNative := SourceEval.Evaluator.cache_hit_native overflowTable .Empty .Empty maxWitness
    (by simp [overflowTable, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native overflowTable .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [overflowTable, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, final, after,
    _, machine, scope, _, inspection, stable⟩ :=
    SourceEval.Evaluator.entry_pair_root_score_scope_complete (external := [6, 7, 8, 9, 10])
      (by simp [World.WellFormed, rootOverflowWorld, overflowWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty (.Pair .Empty .Empty) overflowTable overflowTable overflowTable maxWitness SourceEval.Evaluator.emptyWitness
      4294967295#u32 pairCell largerPairCell overflowCell root_overflow_pair_readable larger_pair_readable root_overflow_table_readable
      footprint root_overflow_resources.1 root_overflow_resources.2
      (by simp [overflowTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl)) headNative tailNative (by decide +kernel)
  refine ⟨final, after, machine, scope, ?_, ?_⟩
  · simpa [SourceEval.checkedAdd32] using scope.result
  · simpa [SourceEval.checkedAdd32, SourceEval.Evaluator.numberKey] using inspection


-- The matched candidate is constructed through all seven actual prefixes.
-- Both queries alias table-owned data, and both smaller contracts are proved.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.MatchedScope SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness headMemo 1#u32 after ∧
    after.state 64 = Slot.ofValue (encodeResult ⟨.Pair .Empty .Empty, 1#u32⟩) ∧
    (after.state 37).dropWork.boxes = 0 ∧ (after.state 47).dropWork.boxes = 0 ∧
    (∀ slot ∈ [59, 61, 65, 66, 67, 68, 69, 70], after.roots slot = none) ∧
    (∀ slot ∈ [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], after.roots slot = none) ∧
    ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix entered active lookupWorld lookupActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions lookupWorld lookupActive missWorld missActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions missWorld missActive headWorld headActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions headWorld headActive tailWorld tailActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions tailWorld tailActive scoreWorld scoreActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rootScoreCases SourceEval.Evaluator.rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
      Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 30) (SourceEval.Evaluator.matchedActions.take 30) rootWorld rootActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, final, after,
    _, machine, scope, _, retired, unbound, _, stable⟩ :=
    SourceEval.Evaluator.entry_pair_matched_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
  refine ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, final, after,
    machine, scope, ?_, ?_, ?_, retired, unbound, stable⟩
  · simpa [SourceEval.Evaluator.matchedWitness, SourceEval.Evaluator.emptyWitness] using scope.candidate
  · rw [scope.headHole]; exact SourceEval.Evaluator.resultWordHole_boxes_zero _
  · rw [scope.tailHole]; exact SourceEval.Evaluator.resultWordHole_boxes_zero _

private def wideWitness : CommonEmbedding := ⟨.Pair .Empty .Empty, 7#u32⟩
private def wideEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 1 [.owned 6, .owned 7], .number wideWitness.edges.val]]
private def wideTable : MemoTable := .Entry ⟨.Empty, .Empty, wideWitness⟩ table
private def wideCell : Cell := .node .table 1 [.owned 4, .owned 5]
private def wideWorld : World := ⟨world.memory ++ [wideEntry, tableCell, .node .word 0 [], .node .word 0 []],
  fun address => if address < 8 then some .box else none, fun address => decide (address < 8)⟩
private theorem wide_extends : Heap.Extends world.memory wideWorld.memory := Heap.Extends.append _ _
private theorem wide_entry_graph : Graph wideWorld.memory wideEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult wideWitness]) [6, 7] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number _) .nil))) .nil)))
private theorem wide_entry_footprint : Footprint wideWorld.memory wideEntry [6, 7] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number _) .nil))) .nil)))
private theorem wide_footprint : Footprint wideWorld.memory wideCell [6, 7, 4, 2, 3, 0, 1, 5] :=
  .node (.cons (.owned rfl wide_entry_footprint) (.cons (.owned rfl
    (.node (.cons (.owned rfl (Heap.Spatial.footprint_mono wide_extends entry_footprint)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
private theorem wide_readable : Readable wideWorld.memory wideWorld.live wideCell (encodeTable wideTable) := by
  refine ⟨[6, 7, 4, 2, 3, 0, 1, 5], .node (.cons (.owned rfl wide_entry_graph) (.cons (.owned rfl
    (.node (.cons (.owned rfl (entry_graph.mono wide_extends)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil)), ?_⟩
  simp [AliveOn, wideWorld]
private theorem wide_pair_readable : Readable wideWorld.memory wideWorld.live pairCell (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, wideWorld]⟩
private theorem wide_resources : OwnerFrame wideWorld [6, 7, 4, 2, 3, 0, 1, 5] ∧ BoxCoverage wideWorld [6, 7, 4, 2, 3, 0, 1, 5] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [wideWorld, bound]
  · intro address member
    have bound : address < 8 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [wideWorld, bound]
  · intro address classified _
    have bound : address < 8 := by simpa [wideWorld] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

-- Both cached results own nonempty words. The matched candidate must transfer
-- their four descendant owners and the two new outer Boxes without duplicating
-- table owners or requiring cache soundness or successful physical execution.
example : ∃ final after,
    OriginalLoanMachine wideWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.MatchedScope wideWitness wideWitness wideTable 15#u32 after ∧
    (after.state 64).dropWork.boxes = 6 ∧ after.roots 66 = none ∧ after.roots 68 = none := by
  have footprint : FieldsFootprint wideWorld.memory [pairCell, pairCell, wideCell] [6, 7, 4, 2, 3, 0, 1, 5] :=
    .cons (.shared _) (.cons (.shared _) (.cons wide_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native wideTable .Empty .Empty wideWitness
    (by simp [wideTable, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, final, after,
    _, machine, scope, _, retired, _, _, stable⟩ :=
    SourceEval.Evaluator.entry_pair_matched_scope_complete (by simp [World.WellFormed, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty wideTable wideTable wideTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell wideCell wide_pair_readable wide_pair_readable wide_readable footprint
      (by simpa [callerOwners] using wide_resources.1) (by simpa [callerOwners] using wide_resources.2)
      (by simp [wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
  refine ⟨final, after, machine, scope, ?_, retired 66 (by simp), retired 68 (by simp)⟩
  rw [scope.candidate]
  simp [SourceEval.Evaluator.matchedWitness, wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields,
    Slot.dropWork, dropFields, DropWork.plus]


-- Both query pointers alias table-owned data. The complete eight-prefix path
-- retains their exact snapshots and the owned concatenation result.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive final after,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairQueryScope .Empty .Empty .Empty .Empty after ∧
    after.state 71 = Slot.ofValue (encodeWord .Empty) ∧
    after.roots 72 = none ∧ after.roots 73 = none ∧
      ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rootScoreCases SourceEval.Evaluator.rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 30) (SourceEval.Evaluator.matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 39) ((SourceEval.Evaluator.matchedActions.drop 30).take 9) matchedWorld matchedActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, final, after,
    cost, nativeCost, _, machine, candidate, queries, value, _, _, retired, _, _, _, _, stable⟩ :=
    SourceEval.Evaluator.entry_pair_left_concat_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, final, after,
    machine, queries, value, retired 72 (by simp), retired 73 (by simp), stable⟩

private def concatWorld : World := ⟨world.memory ++ [.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 4, .owned 5],
  .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 7, .owned 8], .node .word 1 [.owned 6, .owned 9]],
  fun address => if address < 11 then some .box else none, fun address => decide (address < 11)⟩
private def concatPairCell : Cell := .shared ⟨10, []⟩
private def concatMemo : MemoTable := .Entry ⟨.Pair .Empty .Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ table
private theorem concat_extends : Heap.Extends world.memory concatWorld.memory := Heap.Extends.append _ _
private theorem concat_table_readable : Readable concatWorld.memory concatWorld.live tableCell (encodeTable table) := by
  obtain ⟨reads, graph, alive⟩ := table_readable
  refine ⟨reads, graph.mono concat_extends, ?_⟩
  intro address member
  have bound : address < 4 := by simpa [world] using alive address member
  simp [concatWorld]; omega
private theorem concat_pair_readable : Readable concatWorld.memory concatWorld.live pairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, concatWorld]⟩
private theorem concat_large_readable : Readable concatWorld.memory concatWorld.live concatPairCell
    (.reference (encodeWord (.Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty)))) :=
  ⟨[4, 5, 6, 7, 8, 9, 10], .shared rfl (.node (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) (.cons (.owned rfl
    (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))),
    by simp [AliveOn, concatWorld]⟩
private theorem concat_resources : OwnerFrame concatWorld ([2, 3, 0, 1] ++ (callerOwners concatWorld [] ++ [4, 5, 6, 7, 8, 9, 10])) ∧
    BoxCoverage concatWorld ([2, 3, 0, 1] ++ (callerOwners concatWorld [] ++ [4, 5, 6, 7, 8, 9, 10])) := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 11 := by simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [concatWorld, bound]
  · intro address member
    have bound : address < 11 := by simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [concatWorld, bound]
  · intro address classified _
    have bound : address < 11 := by simpa [concatWorld] using classified
    simp only [callerOwners, List.flatMap_nil, List.nil_append, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]; omega

-- Both concatenation operands are nonempty. Real recursive concatenation
-- constructs a four-Box word from an external query and a table-owned query.
example : ∃ final after, ∃ nativeCost : LookupSource.Cost,
    OriginalLoanMachine concatWorld [] {} [4, 5, 6, 7, 8, 9, 10] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairQueryScope (.Pair .Empty .Empty) (.Pair .Empty .Empty) .Empty .Empty after ∧
    SourceEval.Evaluator.MatchedScope SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness concatMemo 1#u32 after ∧
    after.state 71 = Slot.ofValue (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) ∧
    (after.state 71).dropWork.boxes = 4 ∧
    nativeCost.events = MemoSource.concatenateEvents (.Pair .Empty .Empty) (.Pair .Empty .Empty) := by
  have footprint : FieldsFootprint concatWorld.memory [concatPairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons (Heap.Spatial.footprint_mono concat_extends
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native concatMemo (.Pair .Empty .Empty) .Empty SourceEval.Evaluator.emptyWitness
    (by simp [concatMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    cost, nativeCost, _, machine, candidate, queries, value, _, _, _, _, events, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_concat_scope_complete (external := [4, 5, 6, 7, 8, 9, 10])
      (by simp [World.WellFormed, concatWorld, world]) (by simp) Callers.nil
      (.Pair .Empty .Empty) (.Pair .Empty .Empty) .Empty .Empty table concatMemo concatMemo
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      concatPairCell pairCell tableCell concat_large_readable concat_pair_readable concat_table_readable footprint
      concat_resources.1 concat_resources.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      headNative tailNative (by decide +kernel) (by decide +kernel)
  refine ⟨final, after, nativeCost, machine, queries, candidate, value, ?_, events⟩
  rw [value]
  simp [OrderedSolver.appendWord, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]


-- Fresh views are constructed from parsed entry while both original queries
-- alias table-owned data. The actual result root remains available for storage.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive final after anchor,
    AnchoredLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [77, 78] 71 .Empty anchor final after ∧
    after.state 77 = .shared (encodeWord .Empty) ∧ after.state 78 = .shared (encodeWord .Empty) ∧
    (∃ binding, after.roots 76 = some binding ∧ Derived.RootLoansAllowed final after [] 76 binding) ∧
      ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rootScoreCases SourceEval.Evaluator.rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 30) (SourceEval.Evaluator.matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 39) ((SourceEval.Evaluator.matchedActions.drop 30).take 9) matchedWorld matchedActive concatWorld concatActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 44) ((SourceEval.Evaluator.matchedActions.drop 39).take 5) concatWorld concatActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, final, after, anchor,
    _, _, _, machine, _, _, _, value77, value78, _, root76, _, _, _, _, stable⟩ :=
    SourceEval.Evaluator.entry_pair_left_word_views_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
  obtain ⟨binding76, bound76, _⟩ := root76
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, final, after, anchor,
    machine, value77, value78, ⟨binding76, bound76, machine.rootLoans bound76 (by decide)⟩, stable⟩

-- Fresh loans into a four-Box owned word retain the original query snapshots.
-- Their precise anchor excludes the owners of the separate matched candidate.
example : ∃ final after anchor,
    AnchoredLoanMachine concatWorld [] {} [4, 5, 6, 7, 8, 9, 10] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (.Pair .Empty (.Pair .Empty .Empty)) anchor final after ∧
    SourceEval.Evaluator.PairQueryScope (.Pair .Empty .Empty) (.Pair .Empty .Empty) .Empty .Empty after ∧
    (after.state 71).dropWork.boxes = 4 ∧
    after.state 77 = .shared (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) ∧
    after.state 78 = .shared (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) ∧
    (∀ binding item, after.roots 64 = some binding → LocalResources final after.frame after.roots after.state 64 item →
      List.Disjoint item.owners anchor.reads) := by
  have footprint : FieldsFootprint concatWorld.memory [concatPairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons (Heap.Spatial.footprint_mono concat_extends
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native concatMemo (.Pair .Empty .Empty) .Empty SourceEval.Evaluator.emptyWitness
    (by simp [concatMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after, anchor,
    _, _, _, machine, _, queries, wordValue, value77, value78, _, _, _, _, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_word_views_complete (external := [4, 5, 6, 7, 8, 9, 10])
      (by simp [World.WellFormed, concatWorld, world]) (by simp) Callers.nil
      (.Pair .Empty .Empty) (.Pair .Empty .Empty) .Empty .Empty table concatMemo concatMemo
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      concatPairCell pairCell tableCell concat_large_readable concat_pair_readable concat_table_readable footprint
      concat_resources.1 concat_resources.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      headNative tailNative (by decide +kernel) (by decide +kernel)
  refine ⟨final, after, anchor, machine, queries, ?_, value77, value78, ?_⟩
  · rw [wordValue]
    simp [OrderedSolver.appendWord, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  · intro binding item root represented
    exact machine.other_owners_avoid_anchor root (by decide) represented


-- All three recursive contracts are proved empty-input instances. Both parent
-- query pointers alias table-owned data, including across the contraction call.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive final after anchor cost,
    AnchoredLoanMachine world [] {} [] [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [77, 78] 71 .Empty anchor final after ∧
    SourceEval.Evaluator.PairQueryScope .Empty .Empty .Empty .Empty after ∧
    after.state 76 = Slot.ofValue (SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness) headMemo) ∧
    after.state 42 = .empty ∧ (∀ slot ∈ [77, 79, 80], after.state slot = .empty) ∧
      ∀ fuel budget, minFuel ≤ fuel → minBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.lookupSwitch SourceEval.Evaluator.commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.missCases SourceEval.Evaluator.missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.headCases SourceEval.Evaluator.headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.tailCases SourceEval.Evaluator.tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.scoreCases SourceEval.Evaluator.scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rootScoreCases SourceEval.Evaluator.rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 30) (SourceEval.Evaluator.matchedActions.take 30) rootWorld rootActive matchedWorld matchedActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 39) ((SourceEval.Evaluator.matchedActions.drop 30).take 9) matchedWorld matchedActive concatWorld concatActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 44) ((SourceEval.Evaluator.matchedActions.drop 39).take 5) concatWorld concatActive viewsWorld viewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 48) ((SourceEval.Evaluator.matchedActions.drop 44).take 4) viewsWorld viewsActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (SourceEval.Evaluator.matchedCode 48)) []
          .evaluate SourceEval.Evaluator.leftContractionArgs 76 = some (final, after, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 49) [.call .evaluate SourceEval.Evaluator.leftContractionArgs 76] argumentWorld argumentActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab,
    final, after, anchor, result, output, cost, _, machine, candidate, queries, _, value, tableMoved, moved, native, _, _, stable⟩ :=
    SourceEval.Evaluator.entry_pair_left_call_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab,
    final, after, anchor, cost, machine, queries, value, tableMoved, moved, stable⟩

-- A typed warm cache supplies nonempty witnesses of score seven. The six-Box
-- matched candidate and exact original queries persist across real recursion.
example : ∃ final after anchor,
    AnchoredLoanMachine wideWorld [] {} [] [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [77, 78] 71 .Empty anchor final after ∧
    SourceEval.Evaluator.MatchedCandidateScope wideWitness wideWitness 15#u32 after ∧
    SourceEval.Evaluator.PairQueryScope .Empty .Empty .Empty .Empty after ∧
    (after.state 64).dropWork.boxes = 6 ∧
    after.state 76 = Slot.ofValue (SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness) wideTable) := by
  have footprint : FieldsFootprint wideWorld.memory [pairCell, pairCell, wideCell] [6, 7, 4, 2, 3, 0, 1, 5] :=
    .cons (.shared _) (.cons (.shared _) (.cons wide_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native wideTable .Empty .Empty wideWitness
    (by simp [wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native wideTable .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [wideTable, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after, anchor,
    result, output, cost, _, machine, candidate, queries, _, value, _, _, native, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_call_complete (by simp [World.WellFormed, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty wideTable wideTable wideTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell wideCell wide_pair_readable wide_pair_readable wide_readable footprint
      (by simpa [callerOwners] using wide_resources.1) (by simpa [callerOwners] using wide_resources.2)
      (by simp [wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  refine ⟨final, after, anchor, machine, candidate, queries, ?_, value⟩
  rw [candidate.candidate]
  simp [SourceEval.Evaluator.matchedWitness, wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields,
    Slot.dropWork, dropFields, DropWork.plus]

private def coldPairWorld : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1]],
  fun address => if address < 3 then some .box else none, fun address => decide (address < 3)⟩
private def coldPairCell : Cell := .shared ⟨2, []⟩
private def coldTableCell : Cell := .node .table 0 []
private def coldHeadMemo : MemoTable := .Entry ⟨.Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ .Empty
private def coldLeftMemo : MemoTable := .Entry ⟨.Empty, .Pair .Empty .Empty, SourceEval.Evaluator.emptyWitness⟩ coldHeadMemo
private theorem cold_pair_readable : Readable coldPairWorld.memory coldPairWorld.live coldPairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[0, 1, 2], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, coldPairWorld]⟩
private theorem cold_pair_resources : OwnerFrame coldPairWorld [0, 1, 2] ∧ BoxCoverage coldPairWorld [0, 1, 2] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [coldPairWorld, bound]
  · intro address member
    have bound : address < 3 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [coldPairWorld, bound]
  · intro address classified _
    have bound : address < 3 := by simpa [coldPairWorld] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

-- A cold parent performs a head miss, tail hit and contraction miss. The
-- recursive empty-miss path inserts a new key while fresh word loans coexist
-- with the repeated external original-query alias and complete Box coverage.
example : ∃ final after anchor,
    AnchoredLoanMachine coldPairWorld [] {} [0, 1, 2] [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [77, 78] 71 .Empty anchor final after ∧
    SourceEval.Evaluator.PairQueryScope .Empty .Empty .Empty .Empty after ∧
    after.state 76 = Slot.ofValue (SourceEval.Evaluator.encodeOutput (some SourceEval.Evaluator.emptyWitness) coldLeftMemo) := by
  have footprint : FieldsFootprint coldPairWorld.memory [coldPairCell, coldPairCell, coldTableCell] [] :=
    .cons (.shared _) (.cons (.shared _) (.cons (.node .nil) .nil))
  have tableRead : Readable coldPairWorld.memory coldPairWorld.live coldTableCell (encodeTable .Empty) :=
    ⟨[], .node .nil, by simp [AliveOn]⟩
  have headNative := SourceEval.Evaluator.empty_native .Empty .Empty .Empty (Or.inl rfl) rfl
  have tailNative := SourceEval.Evaluator.cache_hit_native coldHeadMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.empty_native coldHeadMemo .Empty (.Pair .Empty .Empty) (Or.inl rfl)
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after, anchor,
    result, output, cost, _, machine, candidate, queries, _, value, _, _, native, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_call_complete (external := [0, 1, 2])
      (by simp [World.WellFormed, coldPairWorld]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty .Empty coldHeadMemo coldHeadMemo
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      coldPairCell coldPairCell coldTableCell cold_pair_readable cold_pair_readable tableRead footprint
      (by simpa [callerOwners] using cold_pair_resources.1) (by simpa [callerOwners] using cold_pair_resources.2)
      rfl (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  exact ⟨final, after, anchor, machine, queries, value⟩

end SourceCacheMissSetupTests
