module

public import SubtreeProofs.Rust.SourceLoanSafeMachine
public import SubtreeProofs.Rust.SourceOwnerCallTransfer

/-! Retain native shared-referent safety through whole existing call steps.
Only closed output types are introduced by this rule; argument masks and the
actual caller-preservation/ownership contracts determine the remaining state. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanSafeState.call_closed {call : Calls} (hcall : Types.CallsTyped call)
    {state masks after : State} {function : Function} {args : List Operand} {values : List Value}
    {types : List Ty} {ty : Ty} {cost : Cost}
    (source : SourceEval.operands state args = some (values, masks)) (safe : LoanSafeState masks)
    (typed : SnapshotFieldsTyped values types) (output : Types.callOutput function types = some ty)
    (closed : Borrow.Closed ty) {slot : Nat}
    (run : SourceEval.action call state (.call function args slot) = some (after, cost)) : LoanSafeState after := by
  simp only [SourceEval.action, source, bind, Option.bind] at run
  cases child : call function values with
  | none => simp only [child] at run; cases run
  | some result =>
    rcases result with ⟨value, work⟩
    rw [child] at run
    obtain ⟨rfl, _⟩ := Prod.mk.inj (Option.some.inj run)
    exact safe.set slot (LoanSafe.of_closed (ofValue_typed (hcall function values types value work ty typed output child)) closed)

theorem LoanSafeMachine.advance_call {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active)
    {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady) (owns : Derived.CallsOwn callee)
    (function : Function) (args : List Operand) {slot : Nat} {binding : Binding} {cost : Cost}
    (hb : active.roots slot = some binding)
    (ready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      Derived.TypedReady world function packets)
    (run : Derived.call callee world active callers function args slot = some (final, after, cost))
    (safe : LoanSafeState after.state) : LoanSafeMachine before callers previous external final after := by
  obtain ⟨_, _, _, roots, valid, callersValid, wf, suspended, scan, _, kept⟩ :=
    Derived.call_spec respects h.valid h.callersValid h.wellFormed function args slot ready run
  have same := (scanCallers_spec h.callersValid scan).unique (h.previousCallers.transport h.kept)
  rw [same] at kept
  have resources := Derived.call_owner_resources respects owns h.valid h.callersValid h.wellFormed
    function args slot h.ownerFrame h.coverage ready run
  have bound := Storage.Activation.binding_lt valid (roots ▸ hb)
  have fresh := h.fresh slot binding hb
  refine ⟨h.beforeWellFormed, h.previousCallers, h.kept.trans kept, valid, wf, ?_, by omega, ?_, safe, resources.1, resources.2⟩
  · intro index target ht
    exact h.separate index target (roots ▸ ht)
  · intro index target ht
    exact h.fresh index target (roots ▸ ht)

end SubtreeProofs.Rust.SourceEval.Addressed
