module

public import SubtreeProofs.Rust.SourcePrefixLocals

/-! Reference preparation changes only top-level shared masks. An untouched
unshared node, including a tuple containing copied references, survives every
actual non-call instruction in a constructed prefix. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.unshared_local_same {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {index : Nat} (unshared : ∀ value, active.state index ≠ .shared value)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction actions generalizing world active with
  | nil => cases h; rfl
  | cons act rest ih =>
    cases h with
    | @cons _ middle _ _ current _ _ _ cost run tail =>
      let prepared := active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)
      have preparedValid := Activation.forgetRefs_valid ha ((act :: rest).foldr Control.Tree.step suffix)
      have preparedSame : prepared.state index = active.state index := LoanEnding.forget_unshared _ _ unshared
      have noncall : Derived.instruction callers (world, prepared) act = some ((middle, current), cost) := by
        cases act with
        | call _ _ _ => cases noCalls
        | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact run
      have step := noncall_spec (source := fun _ _ => none) preparedValid hc hw act noncall
      have all := List.all_eq_true.mp unchanged
      have firstSame := (LocalPreservation.action_same index (all act (by simp)) step.source).trans preparedSame
      have currentUnshared : ∀ value, current.state index ≠ .shared value := by rw [firstSame]; exact unshared
      have restNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
        cases act <;> first | exact noCalls | cases noCalls
      exact (ih tail step.valid step.callers step.wellFormed currentUnshared restNoCalls
        (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem _ member)))).trans firstSame

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
