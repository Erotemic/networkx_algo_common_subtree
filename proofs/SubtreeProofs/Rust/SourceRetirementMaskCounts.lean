module

public import SubtreeProofs.Rust.SourceFreshRetirement
public import SubtreeProofs.Rust.SourcePrefixMaskFacts

/-! Actual drop/storage-dead prefixes determine retained owned-cell counts.
Preparation can end references but cannot change those counts. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def retirementBoxStep (boxes : Nat → Nat) : Action → Nat → Nat
  | .drop slot | .storageDead slot => clearBoxCount boxes slot
  | _ => boxes

theorem rootPresence.absent {roots : Roots} {present : Nat → Bool}
    (same : rootPresence roots = present) {slot : Nat} (absent : present slot = false) : roots slot = none := by
  have missing : (roots slot).isSome = false := by change rootPresence roots slot = false; rw [same]; exact absent
  cases root : roots slot with
  | none => rfl
  | some binding => simp [root] at missing

namespace Calling

theorem Prefix.retirement_boxes {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (retire : ∀ act ∈ actions, ∃ slot, act = .drop slot ∨ act = .storageDead slot) :
    (fun slot => (after.state slot).dropWork.boxes) =
      actions.foldl retirementBoxStep (fun slot => (active.state slot).dropWork.boxes) := by
  induction steps with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    obtain ⟨slot, rfl | rfl⟩ := retire act (by simp)
    all_goals
      have checked := noncall_spec (source := fun _ _ => none) (Activation.forgetRefs_valid ha _) hc hw _ run
      have sourceRun := checked.source
      simp only [SourceEval.action, Partial.Locals.drop, Option.some.injEq, Prod.mk.injEq] at sourceRun
      have masks := sourceRun.1
      rw [ih checked.valid checked.callers checked.wellFormed
        (fun instruction member => retire instruction (List.mem_cons_of_mem _ member)), List.foldl_cons]
      congr 1
      rw [← masks]
      exact prepared_clear_box_counts active _ slot

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
