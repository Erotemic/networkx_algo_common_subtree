module

public import SubtreeProofs.Rust.SourceQueryMachine
public import SubtreeProofs.Rust.SourceLocalPreservation

/-! A constructed non-call prefix retains an untouched closed local exactly.
Reference preparation cannot clear such a local; mutation certificates then
compose its source masks through the actual existing instruction executor. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.closed_local_same {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {index : Nat} {ty : Ty} (typed : SlotTyped (active.state index) ty) (closed : Borrow.Closed ty)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction actions generalizing world active with
  | nil => cases h; rfl
  | cons act rest ih =>
    cases h with
    | @cons _ middle _ _ current _ _ _ cost run tail =>
      let prepared := active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)
      have preparedValid := Activation.forgetRefs_valid ha ((act :: rest).foldr Control.Tree.step suffix)
      have preparedSame : prepared.state index = active.state index := LoanEnding.forget_closed _ _ typed closed
      have noncall : Derived.instruction callers (world, prepared) act = some ((middle, current), cost) := by
        cases act with
        | call _ _ _ => cases noCalls
        | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact run
      have step := noncall_spec (source := fun _ _ => none) preparedValid hc hw act noncall
      have all := List.all_eq_true.mp unchanged
      have firstSame := (LocalPreservation.action_same index (all act (by simp)) step.source).trans preparedSame
      have currentTyped : SlotTyped (current.state index) ty := by rw [firstSame]; exact typed
      have restNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
        cases act <;> first | exact noCalls | cases noCalls
      exact (ih tail step.valid step.callers step.wellFormed currentTyped restNoCalls
        (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem _ member)))).trans firstSame

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
