module

public import SubtreeProofs.Rust.SourceHelperCallTotality

/-! Stable constructed helper calls also run through the actual recursive
dispatcher. Only the function being called matters to a local call step;
unrelated interpreted functions in the dispatcher are left unrestricted. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem call_callee_congr (first second : Callees) (function : Function)
    (same : ∀ world guards callers packets, first world guards callers function packets = second world guards callers function packets)
    (world : World) (active : Activation) (callers : List Activation) (args : List Operand) (slot : Nat) :
    call first world active callers function args slot = call second world active callers function args slot := by
  unfold call
  simp_rw [same]

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage

theorem run_helper (program : List TypeReader.Definition) (budget fuel : Nat) (positive : 0 < fuel)
    (function : Function) (helper : interpreted function = false)
    (world : World) (guards : List Nat) (callers : List Activation) (packets : List ValueCell) :
    run program budget fuel world guards callers function packets = Helpers.callee fuel budget world guards callers function packets := by
  cases fuel with
  | zero => omega
  | succ fuel => simp only [run, helper, Bool.false_eq_true, ite_false]

theorem original_helper_call_stable {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (function : Function) (helper : interpreted function = false) (args : List Operand)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {values : List Value} {masks : State} (source : SourceEval.operands active.state args = some (values, masks))
    (empty : masks slot = .empty) {types : List Ty} {ty : Ty}
    (typed : SnapshotFieldsTyped values types) (outputType : Types.callOutput function types = some ty)
    (closed : Borrow.Closed ty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op)
    (loans : Derived.RootLoansAllowed world {active with state := masks} callers slot binding) :
    ∃ minimumFuel minimumBudget final after cost,
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (original budget fuel) world active callers function args slot = some (final, after, cost) ∧
        SourceEval.action (SourceEval.run Certificate.original.body fuel) active.state (.call function args slot) = some (after.state, cost) := by
  obtain ⟨minimumFuel, minimumBudget, final, after, cost, valid, wf, callersValid, frame, coverage, stable⟩ :=
    Derived.helper_call_stable ha hc hw separate hf covered function helper args hb source empty typed outputType closed moves loans
  refine ⟨minimumFuel + 1, minimumBudget, final, after, cost, valid, wf, callersValid, frame, coverage, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨execute, source⟩ := stable fuel budget (by omega) budgetBound
  have same := Derived.call_callee_congr (original budget fuel) (Helpers.callee fuel budget) function
    (run_helper _ budget fuel (by omega) function helper) world active callers args slot
  exact ⟨same.trans execute, source⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive
