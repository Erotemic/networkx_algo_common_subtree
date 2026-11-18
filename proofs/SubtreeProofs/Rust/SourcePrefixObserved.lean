module

public import SubtreeProofs.Rust.SourcePrefixLocals

/-! A still-observed local survives reference preparation and untouched actual
non-call instructions. The observation premises refer to every real remaining
continuation, including later calls beyond the constructed prefix. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.observed_local_same {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {index : Nat}
    (observed : ∀ offset, offset < actions.length →
      LoanEnding.endsBeforeObservation index ((actions.drop offset).foldr Control.Tree.step suffix) = false)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true)
    (unchanged : actions.all (LocalPreservation.action index) = true) : after.state index = active.state index := by
  induction actions generalizing world active with
  | nil => cases h; rfl
  | cons act rest ih =>
    cases h with
    | @cons _ middle _ _ current _ _ _ cost run tail =>
      let code := (act :: rest).foldr Control.Tree.step suffix
      let prepared := active.forgetRefs code
      have preparedValid := Activation.forgetRefs_valid ha code
      have observedNow : LoanEnding.endsBeforeObservation index code = false := by
        simpa only [List.drop_zero] using observed 0 (by simp)
      have preparedSame : prepared.state index = active.state index := Activation.forgetRefs_observed active code index observedNow
      have noncall : Derived.instruction callers (world, prepared) act = some ((middle, current), cost) := by
        cases act with
        | call _ _ _ => cases noCalls
        | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact run
      have step := noncall_spec (source := fun _ _ => none) preparedValid hc hw act noncall
      have all := List.all_eq_true.mp unchanged
      have firstSame := (LocalPreservation.action_same index (all act (by simp)) step.source).trans preparedSame
      have restObserved : ∀ offset, offset < rest.length →
          LoanEnding.endsBeforeObservation index ((rest.drop offset).foldr Control.Tree.step suffix) = false := by
        intro offset bound
        simpa only [List.drop_succ_cons] using observed (offset + 1) (by simp only [List.length_cons]; omega)
      have restNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
        cases act <;> first | exact noCalls | cases noCalls
      exact (ih tail step.valid step.callers step.wellFormed restObserved restNoCalls
        (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem _ member)))).trans firstSame

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
