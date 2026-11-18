module

public import SubtreeProofs.Rust.SourcePrefixLocals

/-! Actual non-call prefixes preserve activation identity and local count,
including continuation-aware reference preparation and storage retirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.frame_count {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true) :
    after.frame = active.frame ∧ after.count = active.count := by
  induction actions generalizing world active with
  | nil => cases h; exact ⟨rfl, rfl⟩
  | cons act rest ih => cases h with
    | @cons _ middle _ _ current _ _ _ cost run tail =>
      let prepared := active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)
      have noncall : Derived.instruction callers (world, prepared) act = some ((middle, current), cost) := by
        cases act with
        | call _ _ _ => cases noCalls
        | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact run
      have step := noncall_spec (source := fun _ _ => none) (Activation.forgetRefs_valid ha _) hc hw act noncall
      have restNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
        cases act <;> first | exact noCalls | cases noCalls
      have next := ih tail step.valid step.callers step.wellFormed restNoCalls
      exact ⟨next.1.trans step.frame, next.2.trans step.count⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
