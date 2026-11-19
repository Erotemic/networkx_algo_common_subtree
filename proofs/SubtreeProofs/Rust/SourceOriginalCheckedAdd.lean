module

public import SubtreeProofs.Rust.SourceRecursiveHelperCallTotality
public import SubtreeProofs.Rust.SourceOriginalLoanCalls
public import SubtreeProofs.Rust.SourceCacheHitProgram

/-! Actual checked scalar addition at arbitrary explicit local slots. Typed
helper totality constructs one stable call/store; source reflection identifies
its exact native-width result, overflow case and complete source cost. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def numberCallArgs (left right : Nat) : List Operand := [.move (.local left), .move (.local right)]
def numberCallMasks (left right : Nat) (state : State) : State := (state.set left .empty).set right .empty

theorem number_call_arguments {state : State} (l r : Nat) (different : l ≠ r) (left right : Nat)
    (first : state l = .number left) (second : state r = .number right) :
    SourceEval.operands state (numberCallArgs l r) = some ([.number left, .number right], numberCallMasks l r state) := by
  have one := move_local_source (state := state) (slot := l) (value := .number left) (by rw [first]; simp only [Slot.materialize])
  have two := move_local_source (state := state.set l .empty) (slot := r) (value := .number right)
    (by simp only [Partial.Locals.set, Ne.symm different, ite_false, second, Slot.materialize])
  simp only [numberCallArgs, SourceEval.operands, one, two, bind, Option.bind]
  rfl

def checkedAddCallCost (args : List Operand) (destination : Nat) : Cost :=
  (Cost.local (Action.call .checkedAdd args destination).weight).plus (Cost.entry .checkedAdd)

def numberCallCost (l r destination : Nat) : Cost := checkedAddCallCost (numberCallArgs l r) destination

theorem original_checked_add_operands_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (args : List Operand) (inlineArgs : ∀ op ∈ args, InlineOperand op) {masks : State} {destination : Nat}
    (outside : destination ∉ exceptions) (bounded : ∀ index ∈ exceptions, index < active.count)
    (left right : Nat) (leftWidth : left < 2^32) (rightWidth : right < 2^32)
    (arguments : SourceEval.operands active.state args = some ([.number left, .number right], masks))
    (safe : LoanSafeState masks) (closedMiddle : ClosedOutside exceptions masks)
    (family : ∀ index ∈ exceptions, masks index = active.state index ∨ masks index = .empty)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (emptyMasks : masks destination = .empty) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = masks.set destination
        (Slot.ofValue (encodeNumberOption (checkedAdd32 left right))) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .checkedAdd args destination =
          some (final, after, checkedAddCallCost args destination) := by
  have moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    exact h.moves scanned callerView (inlineArgs op member)
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := destination)
    (active := {active with state := masks}) safe raw (Or.inl rfl)
    h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh destination binding root)
  have typed : SnapshotFieldsTyped [.number left, .number right] [.u32, .u32] :=
    .cons (.number leftWidth) (.cons (.number rightWidth) .nil)
  have outputType : Types.callOutput .checkedAdd [.u32, .u32] = some (.option .u32) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  obtain ⟨minFuel, minBudget, final, after, cost, _, _, _, _, _, stable⟩ :=
    Recursive.original_helper_call_stable h.native.valid h.native.callersValid h.native.wellFormed h.native.separate
      h.native.ownerFrame h.native.coverage .checkedAdd rfl args root arguments emptyMasks typed outputType
      (.option .u32) moves loans
  let sufficient := max minFuel 1
  have execute := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).1
  have source := (stable sufficient minBudget (Nat.le_max_left _ _) (by rfl)).2
  have sourceCall : SourceEval.run Certificate.original.body sufficient .checkedAdd [.number left, .number right] =
      some (encodeNumberOption (checkedAdd32 left right), Cost.entry .checkedAdd) := by
    cases enough : sufficient with
    | zero => have positive : 1 ≤ sufficient := Nat.le_max_right _ _; omega
    | succ fuel => exact (Helpers.checkedAdd_total fuel h.native.wellFormed left right leftWidth rightWidth).2.1
  rw [SourceEval.action, arguments] at source
  simp only [bind, Option.bind] at source
  rw [sourceCall] at source
  have same := Prod.mk.inj (Option.some.inj source)
  have state := same.1.symm
  have costEq : cost = checkedAddCallCost args destination := same.2.symm
  have ready := Derived.call_ready_from_values (callers := callers) h.native.valid arguments typed outputType
  have checked := Derived.call_spec (Recursive.original_typed_respects minBudget sufficient)
    h.native.valid h.native.callersValid h.native.wellFormed .checkedAdd args destination ready execute
  have outputTyped := Types.checkedAdd32_typed left right
  have original := h.advance_call (Recursive.original_typed_respects minBudget sufficient) (Recursive.original_owns minBudget sufficient)
    .checkedAdd args root outside ready arguments safe closedMiddle family
    bounded outputTyped (.option .u32) state execute
  refine ⟨sufficient, minBudget, final, after, original, checked.2.2.2.1, checked.2.2.1, checked.2.1, state, ?_, ?_⟩
  · intro slot other different bound raw memoryRead
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects minBudget sufficient)
      h.native.valid h.native.callersValid h.native.wellFormed .checkedAdd args destination ready execute different bound
    exact kept.reads other.address (by simp) raw memoryRead
  · intro fuel budget fuelBound budgetBound
    simpa only [costEq] using (stable fuel budget ((Nat.le_max_left _ _).trans fuelBound) budgetBound).1

theorem original_checked_add_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (l r destination : Nat) (lr : l ≠ r) (dl : destination ≠ l) (dr : destination ≠ r)
    (outside : destination ∉ exceptions) (bounded : ∀ index ∈ exceptions, index < active.count)
    (left right : Nat) (leftWidth : left < 2^32) (rightWidth : right < 2^32)
    (first : active.state l = .number left) (second : active.state r = .number right)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = (numberCallMasks l r active.state).set destination
        (Slot.ofValue (encodeNumberOption (checkedAdd32 left right))) ∧
      (∀ slot binding, slot ≠ destination → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Derived.call (Recursive.original budget fuel) world active callers .checkedAdd (numberCallArgs l r) destination =
          some (final, after, numberCallCost l r destination) := by
  apply original_checked_add_operands_complete h (numberCallArgs l r)
    (by intro op member; simp only [numberCallArgs, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial)
    outside bounded left right leftWidth rightWidth (number_call_arguments l r lr left right first second)
    ((h.native.safe.clear l).clear r) ((h.closed.clear l).clear r) ?_ root raw ?_
  · intro index member
    by_cases one : index = l
    · subst index; right; simp [numberCallMasks, Partial.Locals.set]
    by_cases two : index = r
    · subst index; right; simp [numberCallMasks, Partial.Locals.set]
    · left; simp only [numberCallMasks, Partial.Locals.set, one, two, ite_false]
  · simpa only [numberCallMasks, Partial.Locals.set, dl, dr, ite_false] using empty

end SubtreeProofs.Rust.SourceEval.Evaluator
