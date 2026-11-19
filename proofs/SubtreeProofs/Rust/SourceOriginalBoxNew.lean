module

public import SubtreeProofs.Rust.SourceOriginalCheckedAdd

/-! Construct an actual owned Box helper call from a closed local value. The
native helper and checked result store transfer the input owners and one new
Box, retaining original query loans and one stable complete call cost. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def boxNewCallCost (source destination : Nat) : Cost :=
  (Cost.local (Action.call .boxNew [.move (.local source)] destination).weight).plus (Cost.entry .boxNew)

theorem original_box_new_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (source destination : Nat) (different : destination ≠ source)
    (sourceOutside : source ∉ exceptions) (outside : destination ∉ exceptions)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    {value : Value} {ty : Ty} (initialized : active.state source = Slot.ofValue value)
    (typed : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = (active.state.set source .empty).set destination (Slot.ofValue (.boxed value)) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .boxNew [.move (.local source)] destination =
          some (final, after, boxNewCallCost source destination) := by
  have one := move_local_source (state := active.state) (slot := source) (by rw [initialized]; exact Slot.materialize_ofValue value)
  have arguments : SourceEval.operands active.state [.move (.local source)] = some ([value], active.state.set source .empty) := by
    simp only [SourceEval.operands, one, bind, Option.bind]
  have emptyMasks : (active.state.set source .empty) destination = .empty := by simpa only [Partial.Locals.set, different, ite_false] using empty
  have safe := h.native.safe.clear source
  have moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ [.move (.local source)], Allowed world active.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    have same : op = .move (.local source) := by simpa using member
    subst op; exact h.moves scanned callerView trivial
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := destination)
    (active := {active with state := active.state.set source .empty}) safe raw (Or.inl rfl)
    h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh destination binding root)
  have argsTyped : SnapshotFieldsTyped [value] [ty] := .cons typed .nil
  have outputType : Types.callOutput .boxNew [ty] = some (.owned ty) := by simp only [Types.callOutput, ite_true]
  obtain ⟨minFuel, minBudget, final, after, cost, _, _, _, _, _, stable⟩ :=
    Recursive.original_helper_call_stable h.native.valid h.native.callersValid h.native.wellFormed h.native.separate
      h.native.ownerFrame h.native.coverage .boxNew rfl [.move (.local source)] root arguments emptyMasks argsTyped outputType
      (.owned closed) moves loans
  let sufficient := max minFuel 1
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).1
  have sourceRun := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).2
  have sourceCall : SourceEval.run Certificate.original.body sufficient .boxNew [value] = some (.boxed value, Cost.entry .boxNew) := by
    cases enough : sufficient with
    | zero => have positive : 1 ≤ sufficient := Nat.le_max_right _ _; omega
    | succ fuel => rfl
  rw [SourceEval.action, arguments] at sourceRun
  simp only [bind, Option.bind] at sourceRun
  rw [sourceCall] at sourceRun
  have same := Prod.mk.inj (Option.some.inj sourceRun)
  have state := same.1.symm
  have costEq : cost = boxNewCallCost source destination := same.2.symm
  have ready := Derived.call_ready_from_values (callers := callers) h.native.valid arguments argsTyped outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects minBudget sufficient)
    h.native.valid h.native.callersValid h.native.wellFormed .boxNew [.move (.local source)] destination ready execute
  have original := h.advance_call (Recursive.original_typed_respects minBudget sufficient) (Recursive.original_owns minBudget sufficient)
    .boxNew [.move (.local source)] root outside ready arguments safe (h.closed.clear source)
    (by intro index member; left
        have other : index ≠ source := by intro same; subst index; exact sourceOutside member
        simp only [Partial.Locals.set, other, ite_false]) bounded (.owned typed) (.owned closed) state execute
  refine ⟨sufficient, minBudget, final, after, original, checked.2.2.2.1, checked.2.2.1, checked.2.1, state, ?_, ?_⟩
  · intro slot other notDestination bound raw memoryRead
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects minBudget sufficient)
      h.native.valid h.native.callersValid h.native.wellFormed .boxNew [.move (.local source)] destination ready execute notDestination bound
    exact kept.reads other.address (by simp) raw memoryRead
  · intro fuel budget fuelBound budgetBound
    simpa only [costEq] using (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1

end SubtreeProofs.Rust.SourceEval.Evaluator
