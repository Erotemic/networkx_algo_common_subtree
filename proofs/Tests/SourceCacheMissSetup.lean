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
import SubtreeProofs.Rust.SourcePairLeftScopeEntry
import SubtreeProofs.Rust.SourcePairRightPrefixEntry
import SubtreeProofs.Rust.SourcePairRightScopeEntry
import SubtreeProofs.Rust.SourceOriginalConcatenateFresh
import SubtreeProofs.Rust.SourcePairMatchedFreshEntry
import SubtreeProofs.Rust.SourcePairLeftFreshEntry
import SubtreeProofs.Rust.SourcePairRightFreshPayload
import SubtreeProofs.Rust.SourcePairRightProvenanceEntry
import SubtreeProofs.Rust.SourcePairFinishProvenance
import SubtreeProofs.Rust.SourcePairFinishChoices
import SubtreeProofs.Rust.SourcePairFinishInsertion
import SubtreeProofs.Rust.SourcePairFinishPacking
import SubtreeProofs.Rust.SourcePairRightStorageEntry
import SubtreeProofs.Rust.SourcePairFinishPayload

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


-- All sixty actual matched/left-contraction instructions compose. Ended
-- reference masks restore original loan origins before real root retirement.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive final after cost,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairLeftScope .Empty .Empty .Empty .Empty SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      1#u32 (some SourceEval.Evaluator.emptyWitness) headMemo final after ∧
    (∀ slot, 82 ≤ slot → after.roots slot = none) ∧
    Derived.scrutinee final after [] (.discriminant (.local 74)) = some (.variant .optional 1, after) ∧
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
          .evaluate SourceEval.Evaluator.leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 49) [.call .evaluate SourceEval.Evaluator.leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases ((SourceEval.Evaluator.matchedActions.drop 49).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases SourceEval.Evaluator.matchedActions rootWorld rootActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    final, after, result, output, cost, _, machine, scope, native, inspection, _, future, prefixes⟩ :=
    SourceEval.Evaluator.entry_pair_left_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    final, after, cost, machine, scope, future, inspection, prefixes⟩

-- Real argument/root retirement preserves the six-Box matched candidate,
-- native output fields and the table-owned original query aliases.
example : ∃ final after,
    OriginalLoanMachine wideWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairLeftScope .Empty .Empty .Empty .Empty wideWitness wideWitness 15#u32
      (some SourceEval.Evaluator.emptyWitness) wideTable final after ∧
    (after.state 64).dropWork.boxes = 6 ∧ (∀ slot ∈ [76, 77, 78, 79, 80], after.roots slot = none) := by
  have footprint : FieldsFootprint wideWorld.memory [pairCell, pairCell, wideCell] [6, 7, 4, 2, 3, 0, 1, 5] :=
    .cons (.shared _) (.cons (.shared _) (.cons wide_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native wideTable .Empty .Empty wideWitness
    (by simp [wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native wideTable .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [wideTable, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    result, output, cost, _, machine, scope, native, _, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_scope_complete (by simp [World.WellFormed, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty wideTable wideTable wideTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell wideCell wide_pair_readable wide_pair_readable wide_readable footprint
      (by simpa [callerOwners] using wide_resources.1) (by simpa [callerOwners] using wide_resources.2)
      (by simp [wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  refine ⟨final, after, machine, scope, ?_, scope.retired⟩
  rw [scope.matched.candidate]
  simp [SourceEval.Evaluator.matchedWitness, wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields,
    Slot.dropWork, dropFields, DropWork.plus]

-- Cold recursive insertion now reaches the parent optional switch with both
-- inserted native entries in 75 and fresh empty bound payload storage 81.
example : ∃ final after,
    OriginalLoanMachine coldPairWorld [] {} [0, 1, 2] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    after.state 74 = Slot.ofValue (encodeOption (some SourceEval.Evaluator.emptyWitness)) ∧
    after.state 75 = Slot.ofValue (encodeTable coldLeftMemo) ∧
    (∃ binding, after.roots 81 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
    Derived.scrutinee final after [] (.discriminant (.local 74)) = some (.variant .optional 1, after) := by
  have footprint : FieldsFootprint coldPairWorld.memory [coldPairCell, coldPairCell, coldTableCell] [] :=
    .cons (.shared _) (.cons (.shared _) (.cons (.node .nil) .nil))
  have tableRead : Readable coldPairWorld.memory coldPairWorld.live coldTableCell (encodeTable .Empty) :=
    ⟨[], .node .nil, by simp [AliveOn]⟩
  have headNative := SourceEval.Evaluator.empty_native .Empty .Empty .Empty (Or.inl rfl) rfl
  have tailNative := SourceEval.Evaluator.cache_hit_native coldHeadMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.empty_native coldHeadMemo .Empty (.Pair .Empty .Empty) (Or.inl rfl)
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    result, output, cost, _, machine, scope, native, inspection, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_scope_complete (external := [0, 1, 2])
      (by simp [World.WellFormed, coldPairWorld]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty .Empty coldHeadMemo coldHeadMemo
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      coldPairCell coldPairCell coldTableCell cold_pair_readable cold_pair_readable tableRead footprint
      (by simpa [callerOwners] using cold_pair_resources.1) (by simpa [callerOwners] using cold_pair_resources.2)
      rfl (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  exact ⟨final, after, machine, scope.resultValue, scope.tableValue, scope.payloadRoot, inspection⟩

-- Thirteen actual prefix checkpoints construct the successful left payload
-- and owned right query while retaining repeated table-owned original aliases.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive leftWorld leftActive final after cost,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RightConcatScope .Empty .Empty .Empty .Empty SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      SourceEval.Evaluator.emptyWitness headMemo 1#u32 after ∧
    (∀ slot, 88 ≤ slot → after.roots slot = none) ∧
    Derived.scrutinee leftWorld leftActive [] (.discriminant (.local 74)) = some (.variant .optional 1, leftActive) ∧
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
          .evaluate SourceEval.Evaluator.leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 49) [.call .evaluate SourceEval.Evaluator.leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases ((SourceEval.Evaluator.matchedActions.drop 49).take 11) callWorld callActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases SourceEval.Evaluator.matchedActions rootWorld rootActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.rightCode 15) (SourceEval.Evaluator.rightActions.take 15) leftWorld leftActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    leftWorld, leftActive, final, after, _, _, cost, _, machine, scope, inspection, _, future, _, _, prefixes⟩ :=
    SourceEval.Evaluator.entry_pair_right_prefix_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
      SourceEval.Evaluator.emptyWitness headMemo leftNative
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    leftWorld, leftActive, final, after, cost, machine, scope, future, inspection, prefixes⟩


private def leftWideEntry : Cell := .node .entry 0 [.node .word 0 [], .node .word 1 [.owned 12, .owned 13],
  .node .embedding 0 [.node .word 1 [.owned 10, .owned 11], .number wideWitness.edges.val]]
private def leftWideTable : MemoTable := .Entry ⟨.Empty, .Pair .Empty .Empty, wideWitness⟩ wideTable
private def leftWideCell : Cell := .node .table 1 [.owned 8, .owned 9]
private def leftWideWorld : World := ⟨wideWorld.memory ++ [leftWideEntry, wideCell, .node .word 0 [],
  .node .word 0 [], .node .word 0 [], .node .word 0 []],
  fun address => if address < 14 then some .box else none, fun address => decide (address < 14)⟩
private theorem left_wide_extends : Heap.Extends wideWorld.memory leftWideWorld.memory := Heap.Extends.append _ _
private theorem left_wide_entry_graph : Graph leftWideWorld.memory leftWideEntry
    (.node .entry 0 [encodeWord .Empty, encodeWord (.Pair .Empty .Empty), encodeResult wideWitness]) [12, 13, 10, 11] :=
  .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
    (.cons (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))
private theorem left_wide_entry_footprint : Footprint leftWideWorld.memory leftWideEntry [12, 13, 10, 11] :=
  .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
    (.cons (.node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
      (.cons (.number _) .nil))) .nil)))
private theorem left_wide_footprint : Footprint leftWideWorld.memory leftWideCell [12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9] :=
  .node (.cons (.owned rfl left_wide_entry_footprint) (.cons (.owned rfl
    (Heap.Spatial.footprint_mono left_wide_extends wide_footprint)) .nil))
private theorem left_wide_readable : Readable leftWideWorld.memory leftWideWorld.live leftWideCell (encodeTable leftWideTable) := by
  obtain ⟨reads, graph, alive⟩ := wide_readable
  refine ⟨([12, 13, 10, 11] ++ [8]) ++ ((reads ++ [9]) ++ []), .node (.cons (.owned rfl left_wide_entry_graph)
    (.cons (.owned rfl (graph.mono left_wide_extends)) .nil)), ?_⟩
  intro address member
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with early | old | rfl
  · have bound : address < 14 := by omega
    simp [leftWideWorld, bound]
  · have bound : address < 8 := by simpa [wideWorld] using alive address old
    simp [leftWideWorld]; omega
  · simp [leftWideWorld]
private theorem left_wide_pair_readable : Readable leftWideWorld.memory leftWideWorld.live pairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, leftWideWorld]⟩
private theorem left_wide_resources : OwnerFrame leftWideWorld [12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9] ∧
    BoxCoverage leftWideWorld [12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9] := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 14 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [leftWideWorld, bound]
  · intro address member
    have bound : address < 14 := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [leftWideWorld, bound]
  · intro address classified _
    have bound : address < 14 := by simpa [leftWideWorld] using classified
    simp only [List.mem_cons, List.not_mem_nil, or_false]; omega

-- A cached nonempty left witness actually transfers its two Box owners into
-- payload 81, beside the six-Box matched candidate and table-owned aliases.
example : ∃ final after,
    OriginalLoanMachine leftWideWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RightConcatScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness leftWideTable 15#u32 after ∧
    (after.state 81).dropWork.boxes = 2 ∧ (after.state 64).dropWork.boxes = 6 ∧ after.roots 82 = none := by
  have footprint : FieldsFootprint leftWideWorld.memory [pairCell, pairCell, leftWideCell] [12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9] :=
    .cons (.shared _) (.cons (.shared _) (.cons left_wide_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native leftWideTable .Empty .Empty wideWitness
    (by simp [leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native leftWideTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [leftWideTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    _, _, _, _, machine, scope, _, _, _, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_prefix_complete
      (by simp [World.WellFormed, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty leftWideTable leftWideTable leftWideTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell leftWideCell left_wide_pair_readable left_wide_pair_readable left_wide_readable footprint
      (by simpa [callerOwners] using left_wide_resources.1) (by simpa [callerOwners] using left_wide_resources.2)
      (by simp [leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness leftWideTable leftNative
  refine ⟨final, after, machine, scope, ?_, ?_, scope.payload.held.retired 82 (by simp)⟩
  · rw [scope.payload.held.leftWitness]
    simp [wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  · rw [scope.payload.held.matched.candidate]
    simp [SourceEval.Evaluator.matchedWitness, wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields,
      Slot.dropWork, dropFields, DropWork.plus]

private def rightWideLeftMemo : MemoTable := .Entry
  ⟨.Empty, .Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty), SourceEval.Evaluator.emptyWitness⟩ table

-- Nonempty right operands execute real recursive concatenation and retain a
-- four-Box owned query. All three smaller evaluator contracts are empty cases.
example : ∃ final after, ∃ nativeCost : LookupSource.Cost,
    OriginalLoanMachine concatWorld [] {} [4, 5, 6, 7, 8, 9, 10] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RightConcatScope .Empty .Empty (.Pair .Empty .Empty) (.Pair .Empty .Empty)
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness rightWideLeftMemo 1#u32 after ∧
    after.state 85 = Slot.ofValue (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) ∧
    (after.state 85).dropWork.boxes = 4 ∧
    nativeCost.events = MemoSource.concatenateEvents (.Pair .Empty .Empty) (.Pair .Empty .Empty) := by
  have footprint : FieldsFootprint concatWorld.memory [pairCell, concatPairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons (Heap.Spatial.footprint_mono concat_extends
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
  have hit := SourceEval.Evaluator.cache_hit_native table .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.empty_native table .Empty (.Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty)) (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    _, nativeCost, _, _, machine, scope, _, _, _, events, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_prefix_complete (external := [4, 5, 6, 7, 8, 9, 10])
      (by simp [World.WellFormed, concatWorld, world]) (by simp) Callers.nil
      .Empty .Empty (.Pair .Empty .Empty) (.Pair .Empty .Empty) table table table
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      pairCell concatPairCell tableCell concat_pair_readable concat_large_readable concat_table_readable footprint
      concat_resources.1 concat_resources.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair (.Pair .Empty .Empty) (.Pair .Empty .Empty)) (Or.inl rfl))
      SourceEval.Evaluator.emptyWitness rightWideLeftMemo leftNative
  refine ⟨final, after, nativeCost, machine, scope, scope.wordValue, ?_, events⟩
  rw [scope.wordValue]
  simp [OrderedSolver.appendWord, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]

private def rightMemo : MemoTable := .Entry ⟨.Pair .Empty .Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ headMemo

-- All seventeen actual checkpoints, both exact-cost contraction calls and the
-- whole right region are derived with proved smaller empty-input contracts.
example : ∃ entered active minFuel minBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive matchedWorld matchedActive concatWorld concatActive viewsWorld viewsActive argumentWorld argumentActive callWorld callActive leftWorld leftActive rightConcatWorld rightConcatActive rightViewsWorld rightViewsActive rightArgumentWorld rightArgumentActive rightCallWorld rightCallActive final after cost rightCost,
    OriginalLoanMachine world [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairRightScope .Empty .Empty .Empty .Empty SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      SourceEval.Evaluator.emptyWitness 1#u32 (some SourceEval.Evaluator.emptyWitness) rightMemo final after ∧
    (∀ slot, 96 ≤ slot → after.roots slot = none) ∧
    Derived.scrutinee leftWorld leftActive [] (.discriminant (.local 74)) = some (.variant .optional 1, leftActive) ∧
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
          .evaluate SourceEval.Evaluator.leftContractionArgs 76 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.matchedCode 49) [.call .evaluate SourceEval.Evaluator.leftContractionArgs 76] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases ((SourceEval.Evaluator.matchedActions.drop 49).take 11) callWorld callActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.matchedCases SourceEval.Evaluator.matchedActions rootWorld rootActive leftWorld leftActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.rightCode 15) (SourceEval.Evaluator.rightActions.take 15) leftWorld leftActive rightConcatWorld rightConcatActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.rightCode 22) ((SourceEval.Evaluator.rightActions.drop 15).take 7) rightConcatWorld rightConcatActive rightViewsWorld rightViewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.rightCode 24) ((SourceEval.Evaluator.rightActions.drop 22).take 2) rightViewsWorld rightViewsActive rightArgumentWorld rightArgumentActive ∧
        Derived.call (Recursive.original budget fuel) rightArgumentWorld (rightArgumentActive.forgetRefs (SourceEval.Evaluator.rightCode 24)) []
          .evaluate SourceEval.Evaluator.rightContractionArgs 90 = some (rightCallWorld, rightCallActive, rightCost) ∧
        Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.rightCode 25) [.call .evaluate SourceEval.Evaluator.rightContractionArgs 90] rightArgumentWorld rightArgumentActive rightCallWorld rightCallActive ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rightContractionCases ((SourceEval.Evaluator.rightActions.drop 25).take 11) rightCallWorld rightCallActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) [] SourceEval.Evaluator.rightContractionCases SourceEval.Evaluator.rightActions leftWorld leftActive final after := by
  have footprint : FieldsFootprint world.memory [pairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table .Empty .Empty (Or.inl rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native headMemo .Empty (.Pair .Empty .Empty) SourceEval.Evaluator.emptyWitness
    (by simp [headMemo, table, SourceEval.Evaluator.emptyWitness, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.empty_native headMemo (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [headMemo, table, MemoizedOrderedSolver.findResult])
  obtain ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    leftWorld, leftActive, rightConcatWorld, rightConcatActive, rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive,
    final, after, result, output, _, _, cost, rightCost, _, machine, scope, inspection, native, _, _, future, _, _, prefixes⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete (by simp [World.WellFormed, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty table headMemo headMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 pairCell pairCell tableCell pair_readable pair_readable table_readable footprint resources.2.1 resources.2.2
      (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
      SourceEval.Evaluator.emptyWitness headMemo leftNative
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  exact ⟨entered, active, fuel, budget, wl, al, wm, am, wh, ah, wt, aTail, ws, aScore, wr, ar, wc, ac, wv, av, wa, aa, wb, ab, wd, ad,
    leftWorld, leftActive, rightConcatWorld, rightConcatActive, rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive,
    final, after, cost, rightCost, machine, scope, future, inspection, prefixes⟩



private def leftWideRightMemo : MemoTable := .Entry
  ⟨.Pair .Empty .Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ leftWideTable

-- The actual right call and all cleanup retain a nonempty left witness beside
-- the six-Box matched candidate, with original queries aliasing table owners.
example : ∃ final after,
    OriginalLoanMachine leftWideWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.PairRightScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness 15#u32
      (some SourceEval.Evaluator.emptyWitness) leftWideRightMemo final after ∧
    (after.state 81).dropWork.boxes = 2 ∧ (after.state 64).dropWork.boxes = 6 ∧
    (∀ slot ∈ [86, 87, 90, 91, 92, 93, 94], after.roots slot = none) := by
  have footprint : FieldsFootprint leftWideWorld.memory [pairCell, pairCell, leftWideCell] [12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9] :=
    .cons (.shared _) (.cons (.shared _) (.cons left_wide_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native leftWideTable .Empty .Empty wideWitness
    (by simp [leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native leftWideTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.empty_native leftWideTable (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    result, output, _, _, _, _, _, machine, scope, _, native, _, _, _, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete
      (by simp [World.WellFormed, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty leftWideTable leftWideTable leftWideTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell leftWideCell left_wide_pair_readable left_wide_pair_readable left_wide_readable footprint
      (by simpa [callerOwners] using left_wide_resources.1) (by simpa [callerOwners] using left_wide_resources.2)
      (by simp [leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness leftWideTable leftNative
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  refine ⟨final, after, machine, scope, ?_, ?_, ?_⟩
  · rw [scope.held.leftWitness]
    simp [wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  · rw [scope.held.matched.candidate]
    simp [SourceEval.Evaluator.matchedWitness, wideWitness, encodeResult, encodeWord, Slot.ofValue, ofFields,
      Slot.dropWork, dropFields, DropWork.plus]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact scope.retired _ (by simp)

private def coldRightMemo : MemoTable := .Entry
  ⟨.Pair .Empty .Empty, .Empty, SourceEval.Evaluator.emptyWitness⟩ coldLeftMemo

-- A cold head miss, left miss and right miss insert three native table keys.
-- Real cleanup reaches 88/89 and opens payload 95 while external aliases live.
example : ∃ final after,
    OriginalLoanMachine coldPairWorld [] {} [0, 1, 2] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    after.state 88 = Slot.ofValue (encodeOption (some SourceEval.Evaluator.emptyWitness)) ∧
    after.state 89 = Slot.ofValue (encodeTable coldRightMemo) ∧
    (∃ binding, after.roots 95 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
    Derived.scrutinee final after [] (.discriminant (.local 88)) = some (.variant .optional 1, after) := by
  have footprint : FieldsFootprint coldPairWorld.memory [coldPairCell, coldPairCell, coldTableCell] [] :=
    .cons (.shared _) (.cons (.shared _) (.cons (.node .nil) .nil))
  have tableRead : Readable coldPairWorld.memory coldPairWorld.live coldTableCell (encodeTable .Empty) :=
    ⟨[], .node .nil, by simp [AliveOn]⟩
  have headNative := SourceEval.Evaluator.empty_native .Empty .Empty .Empty (Or.inl rfl) rfl
  have tailNative := SourceEval.Evaluator.cache_hit_native coldHeadMemo .Empty .Empty SourceEval.Evaluator.emptyWitness
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.empty_native coldHeadMemo .Empty (.Pair .Empty .Empty) (Or.inl rfl)
    (by simp [coldHeadMemo, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.empty_native coldLeftMemo (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [coldLeftMemo, coldHeadMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    result, output, _, _, _, _, _, machine, scope, _, native, inspection, _, _, _, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete (external := [0, 1, 2])
      (by simp [World.WellFormed, coldPairWorld]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty .Empty coldHeadMemo coldHeadMemo SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness
      0#u32 1#u32 coldPairCell coldPairCell coldTableCell cold_pair_readable cold_pair_readable tableRead footprint
      (by simpa [callerOwners] using cold_pair_resources.1) (by simpa [callerOwners] using cold_pair_resources.2)
      rfl (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) headNative tailNative (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl))
      SourceEval.Evaluator.emptyWitness coldLeftMemo leftNative
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  exact ⟨final, after, machine, scope.resultValue, scope.tableValue, scope.payloadRoot, inspection⟩


-- Actual nonempty concatenation derives fresh descendant owners and a guarded
-- drop of all four result Boxes, retaining original query/table aliases.
example : ∃ final after cost nativeCost discarded,
    OriginalLoanMachine concatWorld [] {} [4, 5, 6, 7, 8, 9, 10] [73, 72, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    LocalOwnersAbove concatWorld.memory.length final after 71 ∧
    after.state 71 = Slot.ofValue (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) ∧
    Derived.drop final after [] 71 = some (final.retire discarded, {after with state := after.state.set 71 .empty}) ∧
    discarded.length = 4 ∧
    OriginalLoanMachine concatWorld [] {} [4, 5, 6, 7, 8, 9, 10] [73, 72, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      (final.retire discarded) {after with state := after.state.set 71 .empty} ∧
    nativeCost.events = MemoSource.concatenateEvents (.Pair .Empty .Empty) (.Pair .Empty .Empty) ∧
    cost = (SourceEval.Cost.local (SourceEval.Action.call .concatenate (SourceEval.Evaluator.concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) := by
  have footprint : FieldsFootprint concatWorld.memory [concatPairCell, pairCell, tableCell] [2, 3, 0, 1] :=
    .cons (.shared _) (.cons (.shared _) (.cons (Heap.Spatial.footprint_mono concat_extends
      (.node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil)))) .nil))
  have headNative := SourceEval.Evaluator.empty_native table (.Pair .Empty .Empty) .Empty (Or.inr rfl)
    (by simp [table, MemoizedOrderedSolver.findResult])
  have tailNative := SourceEval.Evaluator.cache_hit_native concatMemo (.Pair .Empty .Empty) .Empty SourceEval.Evaluator.emptyWitness
    (by simp [concatMemo, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wm, am, _, machine, candidate, queries, count, _, unbound, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_matched_queries_complete (external := [4, 5, 6, 7, 8, 9, 10])
      (by simp [World.WellFormed, concatWorld, world]) (by simp) Callers.nil
      (.Pair .Empty .Empty) (.Pair .Empty .Empty) .Empty .Empty table concatMemo concatMemo
      SourceEval.Evaluator.emptyWitness SourceEval.Evaluator.emptyWitness 0#u32 1#u32
      concatPairCell pairCell tableCell concat_large_readable concat_pair_readable concat_table_readable footprint
      concat_resources.1 concat_resources.2 (by simp [table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      (SourceEval.Evaluator.native_empty_total (.Pair .Empty .Empty) .Empty (Or.inr rfl))
      headNative tailNative (by decide +kernel) (by decide +kernel)
  obtain ⟨wa, aa, arguments, ma, scopeA, _, _, countA, _, _, _⟩ :=
    SourceEval.Evaluator.pair_left_concat_arguments_complete machine (Helpers.callee 0 0) queries candidate
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> exact unbound _ (by simp))
  let observed := aa.forgetRefs (SourceEval.Evaluator.matchedCode 35)
  have mp := ma.prepare (SourceEval.Evaluator.matchedCode 35)
  have first : observed.state 72 = .shared (encodeWord (.Pair .Empty .Empty)) :=
    (Activation.forgetRefs_observed aa (SourceEval.Evaluator.matchedCode 35) 72 (by decide +kernel)).trans scopeA.leftValue
  have second : observed.state 73 = .shared (encodeWord (.Pair .Empty .Empty)) :=
    (Activation.forgetRefs_observed aa (SourceEval.Evaluator.matchedCode 35) 73 (by decide +kernel)).trans scopeA.rightValue
  obtain ⟨binding, root, raw⟩ := scopeA.resultRoot
  obtain ⟨fuel, budget, final, after, cost, nativeCost, finalMachine, _, _, _, state, events, costEq, fresh,
    ⟨discarded, dropRun, dropLength, dropMachine⟩, _, _⟩ :=
    SourceEval.Evaluator.original_concatenate_fresh_complete mp 72 73 71 (by decide) (by decide) (by decide) (by decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
            change _ < aa.count <;> rw [countA, count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1] <;> decide)
      (.Pair .Empty .Empty) (.Pair .Empty .Empty) first second root raw (SourceEval.LoanEnding.forget_empty _ _ scopeA.resultEmpty)
  have value : after.state 71 = Slot.ofValue (encodeWord (.Pair .Empty (.Pair .Empty .Empty))) := by
    simp [state, Partial.Locals.set, OrderedSolver.appendWord]
  refine ⟨final, after, cost, nativeCost, discarded, finalMachine, fresh, value, dropRun, ?_, dropMachine, events, costEq⟩
  rw [dropLength, value]
  simp [encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]

private def finishEntry : Cell := .node .entry 0
  [.node .word 1 [.owned 18, .owned 19], .node .word 0 [],
   .node .embedding 0 [.node .word 1 [.owned 16, .owned 17], .number 7]]
private def finishTable : MemoTable := .Entry ⟨.Pair .Empty .Empty, .Empty, wideWitness⟩ leftWideTable
private def finishCell : Cell := .node .table 1 [.owned 14, .owned 15]
private def finishWorld : World := ⟨leftWideWorld.memory ++ [finishEntry, leftWideCell, .node .word 0 [],
  .node .word 0 [], .node .word 0 [], .node .word 0 []],
  fun address => if address < 20 then some .box else none, fun address => decide (address < 20)⟩
private def finishOwners : List Nat := [18, 19, 16, 17, 14, 12, 13, 10, 11, 8, 6, 7, 4, 2, 3, 0, 1, 5, 9, 15]
private theorem finish_extends : Heap.Extends leftWideWorld.memory finishWorld.memory := Heap.Extends.append _ _
private theorem finish_entry_graph : Graph finishWorld.memory finishEntry
    (.node .entry 0 [encodeWord (.Pair .Empty .Empty), encodeWord .Empty, encodeResult wideWitness]) [18, 19, 16, 17] :=
  .node (.cons (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil)))
    (.cons (.node .nil) (.cons (.node (.cons
      (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number 7) .nil))) .nil)))
private theorem finish_footprint : Footprint finishWorld.memory finishCell finishOwners :=
  .node (.cons (.owned rfl (finish_entry_graph.footprint
    (Borrow.typed_unborrowed (finish_entry_graph.represents.typed
      (.node .entry (.cons (word_typed _) (.cons (word_typed _) (.cons (result_typed _) .nil)))) ) (.adt .entry))))
    (.cons (.owned rfl (Heap.Spatial.footprint_mono finish_extends left_wide_footprint)) .nil))
private theorem finish_resources : OwnerFrame finishWorld finishOwners ∧ BoxCoverage finishWorld finishOwners := by
  refine ⟨⟨by decide +kernel, ?_, ?_⟩, ?_⟩
  · intro address member
    have bound : address < 20 := by simp only [finishOwners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [finishWorld, bound]
  · intro address member
    have bound : address < 20 := by simp only [finishOwners, List.mem_cons, List.not_mem_nil, or_false] at member; omega
    simp [finishWorld, bound]
  · intro address classified _
    have bound : address < 20 := by simpa [finishWorld] using classified
    simp only [finishOwners, List.mem_cons, List.not_mem_nil, or_false]; omega
private theorem finish_readable : Readable finishWorld.memory finishWorld.live finishCell (encodeTable finishTable) := by
  obtain ⟨reads, graph, _⟩ := left_wide_readable
  have first := Graph.owned (address := 14) (show finishWorld.memory[14]? = some finishEntry by rfl) finish_entry_graph
  have second := Graph.owned (address := 15) (show finishWorld.memory[15]? = some leftWideCell by rfl) (graph.mono finish_extends)
  have next := Graph.node (kind := .table) (tag := 1)
    (GraphFields.cons first (GraphFields.cons second (GraphFields.nil (memory := finishWorld.memory))))
  exact readable_of_footprint next.represents
    (Borrow.typed_unborrowed (next.represents.typed (table_typed finishTable)) (.adt .table)) finish_footprint finish_resources.1.alive
private theorem finish_pair_readable : Readable finishWorld.memory finishWorld.live pairCell
    (.reference (encodeWord (.Pair .Empty .Empty))) :=
  ⟨[2, 3, 0], .shared rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))),
    by simp [AliveOn, finishWorld]⟩

-- All child requests hit typed nonempty cached witnesses of score seven.
-- Actual parsed entry reaches right option 88 with a derived bound, then all
-- six real successful-right payload instructions move its two fresh owners to
-- 95. Original queries alias table-owned words; child views end logically.
example : ∃ beforePayload beforeActive final after resources,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.FinishPayloadScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    Calling.Prefix (Helpers.callee 0 0) [] (SourceEval.Evaluator.finishCode 6) (SourceEval.Evaluator.finishActions.take 6)
      beforePayload beforeActive final after ∧
    LocalResources final after.frame after.roots after.state 95 resources ∧ resources.owners.length = 2 ∧
    (∀ address ∈ resources.owners, finishWorld.memory.length ≤ address) ∧ after.roots 96 = none := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.cache_hit_native finishTable (.Pair .Empty .Empty) .Empty wideWitness
    (by simp [finishTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, _, _, _, machine, scope, _, native, _, count, future, _, _, fresh, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete_fresh (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness finishTable leftNative
      (SourceEval.Evaluator.native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  obtain ⟨final, after, steps, finalMachine, payload, bound, _, _, _, _⟩ :=
    SourceEval.Evaluator.pair_finish_payload_complete machine (Helpers.callee 0 0) scope fresh
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide)
      (future 96 (by decide))
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot 95
  have boxes := represented.boxes
  rw [payload.rightWitness] at boxes
  have two : resources.owners.length = 2 := boxes.trans (by with_unfolding_all rfl)
  exact ⟨wp, ap, final, after, resources, finalMachine, payload, steps, represented, two,
    bound resources represented, payload.retired 96 (by simp)⟩


-- The actual matched candidate combines two nonempty cached witnesses. Twenty
-- old table owners and table-owned query aliases remain legal; the candidate's
-- six owners are derived from the two smaller fresh contracts and new shells.
example : ∃ final after resources,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.MatchedScope wideWitness wideWitness finishTable 15#u32 after ∧
    LocalResources final after.frame after.roots after.state 64 resources ∧ resources.owners.length = 6 ∧
    (∀ address ∈ resources.owners, finishWorld.memory.length ≤ address) ∧
    (∀ slot ∈ [65, 66, 67, 68, 69, 70], after.roots slot = none) := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, final, after,
    _, machine, scope, _, retired, _, _, fresh, _⟩ :=
    SourceEval.Evaluator.entry_pair_matched_scope_complete_fresh (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
  obtain ⟨_, frame⟩ := machine.native.valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot 64
  have boxes := represented.boxes
  rw [scope.candidate] at boxes
  have six : resources.owners.length = 6 := boxes.trans (by with_unfolding_all rfl)
  exact ⟨final, after, resources, machine, scope, represented, six, fresh resources represented,
    fun slot member => retired slot (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using Or.inr (Or.inr member))⟩


-- A nonempty left recursive cache result has two fresh owners. Its actual call,
-- eleven cleanup instructions and six payload steps preserve the six-Box
-- matched candidate and transfer the left witness through scratch 82 into 81.
example : ∃ final after leftResources candidateResources,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.RightPayloadScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    LocalResources final after.frame after.roots after.state 81 leftResources ∧ leftResources.owners.length = 2 ∧
    (∀ address ∈ leftResources.owners, finishWorld.memory.length ≤ address) ∧
    LocalResources final after.frame after.roots after.state 64 candidateResources ∧ candidateResources.owners.length = 6 ∧
    (∀ address ∈ candidateResources.owners, finishWorld.memory.length ≤ address) ∧
    LocalOwnersAbove finishWorld.memory.length final after 71 ∧ after.roots 82 = none := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, machine, scope, native, _, count, future, leftFresh, candidateFresh, wordFresh, _⟩ :=
    SourceEval.Evaluator.entry_pair_left_scope_complete_fresh (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans leftNative))
  obtain ⟨final, after, _, finalMachine, payload, _, _, _, leftAbove, candidateAbove, wordAbove, _⟩ :=
    SourceEval.Evaluator.pair_right_payload_complete_fresh machine (Helpers.callee 0 0) scope leftFresh candidateFresh wordFresh
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide) (future 82 (by decide))
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨leftResources, _, leftRep⟩ := frame.inspectSlot 81
  obtain ⟨candidateResources, _, candidateRep⟩ := frame.inspectSlot 64
  have leftBoxes := leftRep.boxes
  rw [payload.held.leftWitness] at leftBoxes
  have candidateBoxes := candidateRep.boxes
  rw [payload.held.matched.candidate] at candidateBoxes
  exact ⟨final, after, leftResources, candidateResources, finalMachine, payload, leftRep,
    leftBoxes.trans (by with_unfolding_all rfl), leftAbove leftResources leftRep, candidateRep,
    candidateBoxes.trans (by with_unfolding_all rfl), candidateAbove candidateResources candidateRep,
    wordAbove, payload.held.retired 82 (by simp)⟩


-- Both contraction calls and all cleanup preserve the constructed candidate
-- and both fresh query words. All three held choices have concrete bounded
-- owner inventories at the actual finishCode 6 continuation.
example : ∃ final after,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.FinishPayloadScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    (∀ slot ∈ [64, 81, 95], ∃ resources,
      LocalResources final after.frame after.roots after.state slot resources ∧
      resources.owners.length = (if slot = 64 then 6 else 2) ∧
      ∀ address ∈ resources.owners, finishWorld.memory.length ≤ address) ∧
    (∀ slot ∈ [71, 85], LocalOwnersAbove finishWorld.memory.length final after slot) := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.cache_hit_native finishTable (.Pair .Empty .Empty) .Empty wideWitness
    (by simp [finishTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, _, _, _, machine, scope, _, native, _, count, future, _, _, fresh, held, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete_provenance (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness finishTable leftNative
      (SourceEval.Evaluator.native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  obtain ⟨final, after, _, finalMachine, payload, rightAbove, heldAbove, _, _, _, _⟩ :=
    SourceEval.Evaluator.pair_finish_payload_complete_provenance machine (Helpers.callee 0 0) scope fresh held
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide) (future 96 (by decide))
  refine ⟨final, after, finalMachine, payload, ?_, ?_⟩
  · intro slot member
    obtain ⟨_, frame⟩ := finalMachine.native.valid.2
    obtain ⟨resources, _, represented⟩ := frame.inspectSlot slot
    have above : LocalOwnersAbove finishWorld.memory.length final after slot := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · exact heldAbove 64 (by simp)
      · exact heldAbove 81 (by simp)
      · exact rightAbove
    refine ⟨resources, represented, ?_, above resources represented⟩
    have boxes := represented.boxes
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · rw [payload.matched.candidate] at boxes
      exact boxes.trans (by with_unfolding_all rfl)
    · rw [payload.leftWitness] at boxes
      exact boxes.trans (by with_unfolding_all rfl)
    · rw [payload.rightWitness] at boxes
      exact boxes.trans (by with_unfolding_all rfl)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact heldAbove 71 (by decide)
    · exact heldAbove 85 (by decide)


-- Parsed entry, both contractions and both actual choices reach insertion.
-- The matched six-Box witness beats both cached two-Box alternatives while
-- original queries still alias the twenty old table owners.
example : ∃ beforeFinish beforeActive final after resources fuel budget,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.FinishChoicesScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    LocalResources final after.frame after.roots after.state 99 resources ∧ resources.owners.length = 6 ∧
    (∀ address ∈ resources.owners, finishWorld.memory.length ≤ address) ∧
    (∀ slot ∈ [71, 85], LocalOwnersAbove finishWorld.memory.length final after slot) ∧
    Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.finishCode 21) (SourceEval.Evaluator.finishActions.take 21)
      beforeFinish beforeActive final after ∧
    (∀ slot ∈ [100, 101, 102, 103], after.roots slot = none) := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.cache_hit_native finishTable (.Pair .Empty .Empty) .Empty wideWitness
    (by simp [finishTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, _, _, _, machine, scope, _, native, _, count, future, _, _, fresh, held, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete_provenance (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness finishTable leftNative
      (SourceEval.Evaluator.native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, final, after, finalMachine, choiceScope, selectedFresh, wordFresh,
    _, _, _, _, stable⟩ :=
    SourceEval.Evaluator.pair_finish_choices_complete machine scope fresh held
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide)
      (by intro slot member
          have bound : 96 ≤ slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
          exact future slot bound)
  obtain ⟨_, _, _, _, whole, _, _⟩ := stable 1 0 (by decide)
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot 99
  have boxes := represented.boxes
  rw [choiceScope.selected] at boxes
  have six : resources.owners.length = 6 := boxes.trans (by with_unfolding_all rfl)
  refine ⟨wp, ap, final, after, resources, 1, 0, finalMachine, choiceScope, represented, six,
    selectedFresh resources represented, wordFresh, whole, ?_⟩
  intro slot member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> exact choiceScope.retired _ (by simp)

-- Actual insertion with two original aliases into a twenty-Box input table.
-- The native inserted table has thirty-two owners; the separately returned
-- six-Box selected witness remains bounded by the original heap boundary.
example : ∃ beforeFinish beforeActive final after selectedResources tableResources fuel budget,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.FinishInsertionScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    LocalResources final after.frame after.roots after.state 99 selectedResources ∧ selectedResources.owners.length = 6 ∧
    (∀ address ∈ selectedResources.owners, finishWorld.memory.length ≤ address) ∧
    LocalResources final after.frame after.roots after.state 104 tableResources ∧ tableResources.owners.length = 32 ∧
    (∀ slot ∈ [71, 85], LocalOwnersAbove finishWorld.memory.length final after slot) ∧
    Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.finishCode 39) (SourceEval.Evaluator.finishActions.take 39)
      beforeFinish beforeActive final after ∧
    (∀ slot ∈ [105, 106, 107, 108, 109], after.state slot = .empty ∧ after.roots slot = none) := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.cache_hit_native finishTable (.Pair .Empty .Empty) .Empty wideWitness
    (by simp [finishTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, _, _, _, machine, scope, _, native, _, count, future, _, _, fresh, held, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_complete_provenance (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness finishTable leftNative
      (SourceEval.Evaluator.native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  obtain ⟨minFuel, minBudget, _, _, _, _, _, _, final, after, _, finalMachine, insertionScope, freshAfter,
    _, _, _, _, stable⟩ :=
    SourceEval.Evaluator.pair_finish_insertion_complete machine scope fresh held
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1]; decide)
      (by intro slot member
          have bound : 96 ≤ slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
          exact future slot bound)
  have whole := (stable minFuel minBudget (by rfl) (by rfl)).2.2.2.2.2
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨selectedResources, _, selectedRep⟩ := frame.inspectSlot 99
  obtain ⟨tableResources, _, tableRep⟩ := frame.inspectSlot 104
  have selectedBoxes := selectedRep.boxes
  rw [insertionScope.selected] at selectedBoxes
  have six : selectedResources.owners.length = 6 := selectedBoxes.trans (by with_unfolding_all rfl)
  have tableBoxes := tableRep.boxes
  rw [insertionScope.tableValue] at tableBoxes
  have thirtyTwo : tableResources.owners.length = 32 := tableBoxes.trans (by with_unfolding_all rfl)
  refine ⟨wp, ap, final, after, selectedResources, tableResources, minFuel, minBudget, finalMachine, insertionScope,
    selectedRep, six, freshAfter 99 (by simp) selectedResources selectedRep, tableRep, thirtyTwo, ?_, whole, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact freshAfter _ (by decide +kernel)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      exact ⟨insertionScope.moved _ (by decide +kernel), insertionScope.retired _ (by decide +kernel)⟩

-- Empty return storage is derived from parsed entry and every actual prior
-- checkpoint. No empty-root premise is supplied to this complete consumer.
example : ∃ beforeFinish beforeActive final after resources fuel budget,
    OriginalLoanMachine finishWorld [] {} [] [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
    SourceEval.Evaluator.FinishPackedScope .Empty .Empty .Empty .Empty wideWitness wideWitness wideWitness wideWitness finishTable 15#u32 after ∧
    LocalResultOwnersAbove finishWorld.memory.length final after 0 ∧
    LocalResources final after.frame after.roots after.state 0 resources ∧ resources.owners.length = 38 ∧
    (∀ slot ∈ [71, 85], LocalOwnersAbove finishWorld.memory.length final after slot) ∧
    Calling.Prefix (Recursive.original budget fuel) [] (SourceEval.Evaluator.finishCode 56) (SourceEval.Evaluator.finishActions.take 56)
      beforeFinish beforeActive final after ∧
    (∀ slot ∈ [99, 104, 110, 111, 112], after.state slot = .empty ∧ after.roots slot = none) := by
  have input : FieldsFootprint finishWorld.memory [pairCell, pairCell, finishCell] finishOwners :=
    .cons (.shared _) (.cons (.shared _) (.cons finish_footprint .nil))
  have hit := SourceEval.Evaluator.cache_hit_native finishTable .Empty .Empty wideWitness
    (by simp [finishTable, leftWideTable, wideTable, MemoizedOrderedSolver.findResult])
  have leftNative := SourceEval.Evaluator.cache_hit_native finishTable .Empty (.Pair .Empty .Empty) wideWitness
    (by simp [finishTable, leftWideTable, MemoizedOrderedSolver.findResult])
  have rightNative := SourceEval.Evaluator.cache_hit_native finishTable (.Pair .Empty .Empty) .Empty wideWitness
    (by simp [finishTable, MemoizedOrderedSolver.findResult])
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, wp, ap,
    result, output, _, _, _, _, _, machine, scope, _, native, _, count, future, _, _, fresh, held, storage, _, _⟩ :=
    SourceEval.Evaluator.entry_pair_right_scope_storage_complete_provenance (external := [])
      (by simp [World.WellFormed, finishWorld, leftWideWorld, wideWorld, world]) (by simp) Callers.nil
      .Empty .Empty .Empty .Empty finishTable finishTable finishTable wideWitness wideWitness 14#u32 15#u32
      pairCell pairCell finishCell finish_pair_readable finish_pair_readable finish_readable input
      (by simpa [callerOwners] using finish_resources.1) (by simpa [callerOwners] using finish_resources.2)
      (by simp [finishTable, leftWideTable, wideTable, table, MemoizedOrderedSolver.findResult])
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl))
      (SourceEval.Evaluator.native_empty_total_fresh .Empty .Empty (Or.inl rfl)) hit hit (by decide +kernel) (by decide +kernel)
      (SourceEval.Evaluator.native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl)) wideWitness finishTable leftNative
      (SourceEval.Evaluator.native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl))
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightNative))
  obtain ⟨root0, bound0, raw0⟩ := storage.root
  obtain ⟨minFuel, minBudget, _, _, _, _, _, _, final, after, finalMachine, packedScope, freshAfter, heldAfter,
    _, _, _, _, stable⟩ :=
    SourceEval.Evaluator.pair_finish_packing_complete machine scope fresh held bound0 raw0 storage.empty
      (by rw [count, SourceEval.CallingCertificate.originalEvaluator_spec.2.1])
      (by intro slot member
          have bound : 96 ≤ slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
          exact future slot bound)
  have whole := (stable minFuel minBudget (by rfl) (by rfl)).2.2.2.2
  obtain ⟨_, frame⟩ := finalMachine.native.valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot 0
  have boxes := represented.boxes
  rw [packedScope.output] at boxes
  have thirtyEight : resources.owners.length = 38 := boxes.trans (by with_unfolding_all rfl)
  refine ⟨wp, ap, final, after, resources, minFuel, minBudget, finalMachine, packedScope, freshAfter,
    represented, thirtyEight, heldAfter, whole, ?_⟩
  intro slot member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl <;>
    exact ⟨packedScope.moved _ (by decide +kernel), packedScope.retired _ (by decide +kernel)⟩

end SourceCacheMissSetupTests
