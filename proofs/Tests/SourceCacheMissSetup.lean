import SubtreeProofs.Rust.SourcePairHeadScopeEntry

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

end SourceCacheMissSetupTests
