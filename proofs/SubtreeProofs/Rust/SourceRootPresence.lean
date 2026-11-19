module

public import SubtreeProofs.Rust.SourcePrefixIdentity

/-! Exact physical root presence follows storage-live/dead, independently of
allocation addresses, logical holes, and the bodies of successful calls. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def rootPresence (roots : Roots) : Nat → Bool := fun slot => (roots slot).isSome

def rootPresenceStep (present : Nat → Bool) : Action → Nat → Bool
  | .storageLive destination => fun slot => if slot = destination then true else present slot
  | .storageDead destination => fun slot => if slot = destination then false else present slot
  | _ => present

def rootSlotsStep (slots : List Nat) : Action → List Nat
  | .storageLive destination => destination :: slots
  | .storageDead destination => slots.filter (· != destination)
  | _ => slots

theorem rootPresenceStep_contains (slots : List Nat) (act : Action) :
    rootPresenceStep (fun slot => slots.contains slot) act = fun slot => (rootSlotsStep slots act).contains slot := by
  funext slot
  cases act <;> simp [rootPresenceStep, rootSlotsStep]
  case storageDead destination =>
    exact Bool.and_comm _ _

theorem rootPresence_fold_contains (slots : List Nat) (actions : List Action) :
    actions.foldl rootPresenceStep (fun slot => slots.contains slot) =
      fun slot => (actions.foldl rootSlotsStep slots).contains slot := by
  induction actions generalizing slots with
  | nil => rfl
  | cons act rest ih =>
    simp only [List.foldl_cons, rootPresenceStep_contains]
    exact ih _

theorem enter_root_presence {world entered : World} {active : Activation} {frame count : Nat} {packets : List ValueCell}
    (run : enter world frame count packets = some (entered, active)) :
    rootPresence active.roots = fun slot => decide (0 < slot ∧ slot ≤ packets.length) := by
  unfold enter at run
  split at run
  next ready =>
    cases run
    funext slot
    simp only [rootPresence, initialActivation, argumentRoots]
    split <;> simp_all
  next => cases run

namespace Derived

theorem action_root_presence {world final : World} {active after : Activation} {callers : List Activation} {act : Action}
    (run : Derived.action world active callers act = some (final, after)) :
    rootPresence after.roots = rootPresenceStep (rootPresence active.roots) act := by
  cases act with
  | storageLive destination =>
    simp only [Derived.action, storageLive] at run
    split at run
    next ready =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨current, scan, suspended, callerScan, run⟩ := run
      cases run
      funext slot
      simp only [rootPresence, rootPresenceStep, Roots.set]
      split <;> rfl
    next => cases run
  | storageDead destination =>
    simp only [Derived.action, storageDead] at run
    split at run
    next zero =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨remainder, suspended⟩, context, binding, root, ending, ended, run⟩ := run
      cases run
      funext slot
      simp only [rootPresence, rootPresenceStep, Roots.set]
      split <;> rfl
    next => cases run
  | assign destination rhs | drop destination | fakeRead place | call function args destination | undefinedBehavior =>
    funext slot
    exact congrArg Option.isSome ((action_shape run).2.2 slot trivial)

end Derived

namespace Calling

theorem instruction_root_presence {callee : Derived.Callees} {world final : World} {active after : Activation}
    {callers : List Activation} {act : Action} {cost : Cost}
    (run : instruction callee callers (world, active) act = some ((final, after), cost)) :
    rootPresence after.roots = rootPresenceStep (rootPresence active.roots) act := by
  cases act with
  | call function args destination =>
    funext slot
    exact congrArg Option.isSome ((instruction_shape run).2.2 slot trivial)
  | storageLive destination | storageDead destination | assign destination rhs | drop destination | fakeRead place | undefinedBehavior =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, run⟩ := run
    cases run
    exact Derived.action_root_presence acted

theorem Prefix.root_presence {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after) :
    rootPresence after.roots = actions.foldl rootPresenceStep (rootPresence active.roots) := by
  induction steps with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    rw [ih, List.foldl_cons, instruction_root_presence run]
    rfl

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
