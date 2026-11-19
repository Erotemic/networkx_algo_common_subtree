module

public import SubtreeProofs.Rust.SourceHelperFuel
public import SubtreeProofs.Rust.SourceControlExtension

/-! More-defined callees preserve exact successful actual calling executions.
All argument scans, loan views, stores, routing, entry and checked cleanup are
unchanged. This is an extension law, not a physical-success assumption. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

namespace Derived

def CallsExtend (first second : Callees) : Prop :=
  ∀ world guards callers function packets final packet cost,
    first world guards callers function packets = some (final, packet, cost) →
    second world guards callers function packets = some (final, packet, cost)

theorem call_extends {first second : Callees} (hc : CallsExtend first second)
    {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {slot : Nat} {cost : Cost}
    (h : call first world active callers function args slot = some (final, after, cost)) :
    call second world active callers function args slot = some (final, after, cost) := by
  simp only [call, bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨current, hcurrent, suspended, hsuspended, ⟨packets, masks⟩, hargs,
    remainder, hrest, binding, hb, ⟨returned, packet, inner⟩, hcall,
    ⟨next, state⟩, hstore, last⟩ := h
  exact ⟨_, hcurrent, _, hsuspended, _, hargs, _, hrest, _, hb,
    _, hc _ _ _ _ _ _ _ _ hcall, _, hstore, last⟩

end Derived

namespace Calling

theorem instruction_extends {first second : Derived.Callees} (hc : Derived.CallsExtend first second)
    {callers : List Activation} {machine after : World × Activation} {action : Action} {cost : Cost}
    (h : instruction first callers machine action = some (after, cost)) :
    instruction second callers machine action = some (after, cost) := by
  cases action with
  | call function args slot =>
    simp only [instruction, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨world, active, inner⟩, run, last⟩ := h
    exact ⟨_, Derived.call_extends hc run, last⟩
  | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior => exact h

theorem exec_extends {first second : Derived.Callees} (hc : Derived.CallsExtend first second)
    {callers : List Activation} {code : Code} {world : World} {active : Activation} {flow : Derived.Flow} {cost : Cost}
    (h : exec first callers code world active = some (flow, cost)) :
    exec second callers code world active = some (flow, cost) :=
  Control.execWith_extends (loanInstruction first callers) (loanInstruction second callers)
    (fun _ _ pair hp => by rcases pair with ⟨next, cost⟩; exact instruction_extends hc hp)
    (Derived.inspectScrutinee callers) (fun machine => Derived.returnValue callers machine.1 machine.2)
    (fun machine => .next machine.1 machine.2) Derived.nextState {} Cost.plus
    (fun scrut => Cost.local (1 + scrut.weight)) (schedule code) h

theorem invoke_extends {first second : Derived.Callees} (hc : Derived.CallsExtend first second)
    {callers : List Activation} {guards : List Nat} {decl : TypeReader.Definition}
    {world final : World} {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : invoke first callers guards decl world packets = some (final, packet, cost)) :
    invoke second callers guards decl world packets = some (final, packet, cost) := by
  unfold invoke at h ⊢
  split at h
  next arity =>
    simp only [arity, ite_true, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨entered, active⟩, he, ⟨flow, work⟩, hx, last⟩ := h
    exact ⟨_, he, _, exec_extends hc hx, last⟩
  next => cases h

theorem guardedInvoke_extends {first second : Derived.Callees} (hc : Derived.CallsExtend first second)
    {callers : List Activation} {guards : List Nat} {decl : TypeReader.Definition}
    {world final : World} {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (h : guardedInvoke first callers guards decl world packets = some (final, packet, cost)) :
    guardedInvoke second callers guards decl world packets = some (final, packet, cost) := by
  simp only [guardedInvoke, bind, Option.bind_eq_some_iff] at h ⊢
  obtain ⟨suspended, hs, last⟩ := h
  refine ⟨_, hs, ?_⟩
  split at last
  next allowed => simpa only [allowed, ite_true] using invoke_extends hc last
  next denied => cases last

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
