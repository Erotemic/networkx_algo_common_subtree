module

public import SubtreeProofs.Rust.SourceCallingPrefixes
public import SubtreeProofs.Rust.SourceEvalCallingControl

/-! Actual instructions preserve activation frame/count even across calls.
Only storage-live/dead change roots. These are executable record-shape facts;
no successful callee postcondition or extra physical readiness is assumed. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def keepsRoot (slot : Nat) : Action → Prop
  | .storageLive destination | .storageDead destination => slot ≠ destination
  | _ => True

instance keepsRoot_decidable (slot : Nat) (act : Action) : Decidable (keepsRoot slot act) := by
  cases act <;> unfold keepsRoot <;> infer_instance

namespace Derived

theorem action_shape {world final : World} {active after : Activation} {callers : List Activation} {act : Action}
    (run : Derived.action world active callers act = some (final, after)) :
    after.frame = active.frame ∧ after.count = active.count ∧
      ∀ slot, keepsRoot slot act → after.roots slot = active.roots slot := by
  cases act with
  | storageLive destination =>
    simp only [Derived.action, storageLive] at run
    split at run
    next ready =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨current, scan, suspended, callerScan, run⟩ := run
      cases run
      exact ⟨rfl, rfl, by intro slot different; simp only [Roots.set, keepsRoot] at different ⊢; simp [different]⟩
    next => cases run
  | storageDead destination =>
    simp only [Derived.action, storageDead] at run
    split at run
    next zero =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨remainder, suspended⟩, context, binding, root, ending, ended, run⟩ := run
      cases run
      exact ⟨rfl, rfl, by intro slot different; simp only [Roots.set, keepsRoot] at different ⊢; simp [different]⟩
    next => cases run
  | assign destination rhs =>
    simp only [Derived.action, assign, bind, Option.bind_eq_some_iff] at run
    obtain ⟨current, scan, suspended, callerScan, ⟨packet, masks⟩, expression, remainder, remaining,
      ⟨ending, state⟩, stored, run⟩ := run
    cases run
    exact ⟨rfl, rfl, by intros; rfl⟩
  | drop destination =>
    simp only [Derived.action, drop, bind, Option.bind_eq_some_iff] at run
    obtain ⟨item, inspected, ⟨remainder, suspended⟩, context, binding, root, run⟩ := run
    split at run
    next ready => cases run; exact ⟨rfl, rfl, by intros; rfl⟩
    next => cases run
  | fakeRead place => cases run; exact ⟨rfl, rfl, by intros; rfl⟩
  | call _ _ _ | undefinedBehavior => cases run

theorem call_shape {callee : Callees} {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {destination : Nat} {cost : Cost}
    (run : Derived.call callee world active callers function args destination = some (final, after, cost)) :
    after.frame = active.frame ∧ after.count = active.count ∧ after.roots = active.roots := by
  simp only [Derived.call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packets, masks⟩, arguments, remainder, remaining, binding, root,
    ⟨returned, packet, inner⟩, called, ⟨ending, state⟩, stored, run⟩ := run
  cases run
  exact ⟨rfl, rfl, rfl⟩

end Derived

namespace Calling

theorem instruction_shape {callee : Derived.Callees} {world final : World} {active after : Activation}
    {callers : List Activation} {act : Action} {cost : Cost}
    (run : instruction callee callers (world, active) act = some ((final, after), cost)) :
    after.frame = active.frame ∧ after.count = active.count ∧
      ∀ slot, keepsRoot slot act → after.roots slot = active.roots slot := by
  cases act with
  | call function args destination =>
    simp only [instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state, inner⟩, called, run⟩ := run
    cases run
    obtain ⟨frame, count, roots⟩ := Derived.call_shape called
    exact ⟨frame, count, by intros; rw [roots]⟩
  | storageLive destination | storageDead destination | assign destination rhs | drop destination | fakeRead place | undefinedBehavior =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, run⟩ := run
    cases run
    exact Derived.action_shape acted

theorem Prefix.shape {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation}
    (h : Prefix callee callers suffix actions world active final after) :
    after.frame = active.frame ∧ after.count = active.count ∧
      ∀ slot, (∀ act ∈ actions, keepsRoot slot act) → after.roots slot = active.roots slot := by
  induction h with
  | nil => exact ⟨rfl, rfl, by intros; rfl⟩
  | @cons world middle final active current after act rest cost run tail ih =>
    have step := instruction_shape run
    refine ⟨ih.1.trans step.1, ih.2.1.trans step.2.1, ?_⟩
    intro slot untouched
    exact (ih.2.2 slot (fun action member => untouched action (List.mem_cons_of_mem act member))).trans
      (step.2.2 slot (untouched act (by simp)))

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
