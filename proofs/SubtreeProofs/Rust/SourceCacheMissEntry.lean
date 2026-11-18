module

public import SubtreeProofs.Rust.SourceCacheMissScope

/-! Parsed native miss entry, all common and miss-setup instructions, and actual
word inspection/routing. Empty and pair/pair branch execution remain separate
from the constructed initialized scope at their boundary. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def wordBranch : BalancedWord → Nat
  | .Empty => 0
  | .Pair _ _ => 1

theorem miss_right_scrutinee_source {state : State} (left right : BalancedWord) (tuple : state 13 = queryTuple left right) :
    SourceEval.scrutinee state (.discriminant (.deref (.field (.local 13) none 1))) = some (wordKey right, state) := by
  cases right <;> simp [SourceEval.scrutinee, splitPlace, tuple, queryTuple, Slot.get, wordKey, encodeWord, Slot.ofValue]

theorem miss_switch_native {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    {left right : BalancedWord} {table : MemoTable} (scope : MissScope initial left right table world active) :
    Derived.scrutinee world active callers (.discriminant (.deref (.field (.local 13) none 0))) = some (wordKey left, active) ∧
    Derived.scrutinee world active callers (.discriminant (.deref (.field (.local 13) none 1))) = some (wordKey right, active) ∧
    Control.selectIndex (wordKey left) [(.variant .word 0, 0)] (some 1) = some (wordBranch left) ∧
    Control.selectIndex (wordKey right) [(.variant .word 0, 0), (.variant .word 1, 1)] none = some (wordBranch right) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only using Derived.scrutinee_complete h.valid h.callersValid _ (miss_scrutinee_source left right scope.tuple) (by intros; trivial)
  · simpa only using Derived.scrutinee_complete h.valid h.callersValid _ (miss_right_scrutinee_source left right scope.tuple) (by intros; trivial)
  · cases left <;> rfl
  · cases right <;> rfl

theorem entry_miss_setup_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table left right = none) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      (∀ slot, slot ∉ [1, 2, 3] → active.roots slot = none) ∧
      LoanSafeMachine world callers previous external final after ∧ MissScope active left right table final after ∧
      QueryOrigins final after world.memory.length ∧ LoanOrigin final after world.memory.length 13 ∧
      ClosedOutside [1, 2, 13] after.state ∧ WordLoanState after.state ∧
      Derived.scrutinee lookupWorld lookupActive callers (.discriminant (.local 4)) = some (.variant .optional 0, lookupActive) ∧
      Derived.scrutinee final after callers (.discriminant (.deref (.field (.local 13) none 0))) = some (wordKey left, after) ∧
      Derived.scrutinee final after callers (.discriminant (.deref (.field (.local 13) none 1))) = some (wordKey right, after) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, entryRun, initialState, count, unbound,
    machine, scope, origins, observed, stable⟩ :=
    entry_common_prefix_complete hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have nativeMiss : (LookupEvents.lookup table left right).1 = none := by rw [LookupEvents.lookup_value]; exact miss
  obtain ⟨final, after, setup, finalMachine, finalScope, finalQueries, tupleOrigin, closed, words⟩ :=
    miss_setup_complete (scope.query_machine machine origins unbound) (Helpers.callee 0 0) scope unbound
      (by rw [scope.count, count]; decide) nativeMiss
  obtain ⟨leftInspection, rightInspection, _, _⟩ := miss_switch_native finalMachine finalScope
  refine ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, final, after, entryRun, unbound,
    finalMachine, finalScope, finalQueries, tupleOrigin, closed, words, ?_, leftInspection, rightInspection, ?_⟩
  · simpa only [nativeMiss, lookupKey] using observed
  · intro fuel budget fuelBound budgetBound
    exact ⟨stable fuel budget fuelBound budgetBound, setup.noncall_callee _ (by decide +kernel)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
