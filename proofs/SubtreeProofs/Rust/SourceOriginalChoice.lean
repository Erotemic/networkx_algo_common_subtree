module

public import SubtreeProofs.Rust.SourceChoiceOwnerProvenance
public import SubtreeProofs.Rust.SourceAggregateOwnerProvenance
public import SubtreeProofs.Rust.SourceOriginalLoanCalls

/-! Construct actual owned choice calls in an original-loan machine. Derived
input owner bounds discharge transfer permission while unrelated original
query/table/caller aliases remain permitted. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem Recursive.original_choice_callee_same (firstBudget firstFuel secondBudget secondFuel : Nat)
    (firstPositive : 0 < firstFuel) (secondPositive : 0 < secondFuel)
    (world : World) (guards : List Nat) (callers : List Activation) (packets : List ValueCell) :
    Recursive.original firstBudget firstFuel world guards callers .chooseLonger packets =
      Recursive.original secondBudget secondFuel world guards callers .chooseLonger packets := by
  cases firstFuel with
  | zero => omega
  | succ firstFuel =>
    cases secondFuel with
    | zero => omega
    | succ secondFuel =>
      simp only [Recursive.original, Recursive.run, Recursive.interpreted, ite_true, CallingCertificate.choice_lookup, bind, Option.bind]
      exact Calling.guardedInvoke_noCalls _ _ callers guards CallingCertificate.originalChoice
        (by rw [CallingCertificate.originalChoice_spec.2.2]; decide +kernel) world packets

theorem OriginalLoanMachine.arguments_loans_of_fresh {before world : World} {active : Activation}
    {callers : List Activation} {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    {args : List Operand} {masks : State}
    (inputs : OperandSourcesAbove before.memory.length world active args)
    (closed : ClosedOutside exceptions masks)
    (family : ∀ index ∈ exceptions, masks index = active.state index) :
    Derived.ArgumentsLoansAllowed world active callers args masks := by
  intro guarded packets owners suspended arguments footprint callerView
  have packetBounds := (operands_owner_provenance args h.native.valid arguments).2 inputs
  have bounds := fields_owner_provenance (by
    intro cell member
    obtain ⟨packet, selected, rfl⟩ := List.mem_map.mp member
    exact packetBounds packet selected) footprint
  cases callerView with
  | cons current old =>
    have origins : ∀ slot ∈ exceptions, LoanOrigin world {active with state := masks} before.memory.length slot := by
      intro slot member
      exact (h.origins slot member).congr rfl rfl (family slot member)
    apply List.disjoint_left.mpr
    intro address owned borrowed
    have above := bounds address owned
    rcases List.mem_append.mp borrowed with localLoan | oldLoan
    · have below := Inventory.loans_below_family current.inventory closed origins address localLoan
      omega
    · have below := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed h.native.kept old
        address (old.loans_subset_reads oldLoan)
      omega

end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def choiceCallCost (left right destination : Nat) (first second : CommonEmbedding) : Cost :=
  (Cost.local (Action.call .chooseLonger [.move (.local left), .move (.local right)] destination).weight).plus
    (Choice.cost first second)

theorem original_choice_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (left right destination : Nat) (different : left ≠ right) (dl : destination ≠ left) (dr : destination ≠ right)
    (leftOutside : left ∉ exceptions) (rightOutside : right ∉ exceptions) (outside : destination ∉ exceptions)
    (bounded : ∀ index ∈ exceptions, index < active.count)
    (first second : CommonEmbedding)
    (leftValue : active.state left = Slot.ofValue (encodeResult first))
    (rightValue : active.state right = Slot.ofValue (encodeResult second))
    (leftAbove : LocalOwnersAbove before.memory.length world active left)
    (rightAbove : LocalOwnersAbove before.memory.length world active right)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ final after,
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state = ((active.state.set left .empty).set right .empty).set destination
        (Slot.ofValue (encodeResult (OrderedSolver.selectResult first second))) ∧
      LocalOwnersAbove before.memory.length final after destination ∧
      (∀ other, other < active.count → other ≠ left → other ≠ right → other ≠ destination →
        LocalOwnersAbove before.memory.length world active other → LocalOwnersAbove before.memory.length final after other) ∧
      (∀ slot other, slot ≠ destination → active.roots slot = some other → ∀ cell,
        world.memory[other.address]? = some cell → final.memory[other.address]? = some cell) ∧
      ∀ fuel budget, 0 < fuel →
        Derived.call (Recursive.original budget fuel) world active callers .chooseLonger
          [.move (.local left), .move (.local right)] destination =
            some (final, after, choiceCallCost left right destination first second) := by
  let args : List Operand := [.move (.local left), .move (.local right)]
  let masks := (active.state.set left .empty).set right .empty
  have one := move_local_source (state := active.state) (slot := left) (by rw [leftValue]; exact Slot.materialize_ofValue _)
  have two := move_local_source (state := active.state.set left .empty) (slot := right) (value := encodeResult second)
    (by simp only [Partial.Locals.set, Ne.symm different, ite_false, rightValue, Slot.materialize_ofValue])
  have source : SourceEval.operands active.state args = some ([encodeResult first, encodeResult second], masks) := by
    simp only [args, masks, SourceEval.operands, one, two, bind, Option.bind]
  have emptyMasks : masks destination = .empty := by
    simpa only [masks, Partial.Locals.set, dl, dr, ite_false] using empty
  have closed : ClosedOutside exceptions masks := (h.closed.clear left).clear right
  have family : ∀ index ∈ exceptions, masks index = active.state index := by
    intro index member
    have notL : index ≠ left := by intro same; subst index; exact leftOutside member
    have notR : index ≠ right := by intro same; subst index; exact rightOutside member
    simp only [masks, Partial.Locals.set, notL, notR, ite_false]
  have inputs : OperandSourcesAbove before.memory.length world active args := OperandSourcesAbove.two_moves leftAbove rightAbove
  have safe : LoanSafeState masks := (h.native.safe.clear left).clear right
  have loans := Derived.RootLoansAllowed.of_safe_preserved (slot := destination) (active := {active with state := masks})
    safe raw (Or.inl rfl) h.native.previousCallers h.native.beforeWellFormed h.native.kept (h.native.fresh destination binding root)
  have moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op := by
    intro current suspended scanned callerView op member
    apply h.moves scanned callerView
    simp only [args, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> trivial
  obtain ⟨final, after, execute, state, _, _, _, _, _, _⟩ := Derived.choice_call_total 0 0
    h.native.valid h.native.callersValid h.native.wellFormed h.native.separate h.native.ownerFrame h.native.coverage
    args root first second source emptyMasks moves loans (h.arguments_loans_of_fresh inputs closed family)
  have typed : SnapshotFieldsTyped [encodeResult first, encodeResult second] [.adt .embedding, .adt .embedding] :=
    .cons (result_typed first) (.cons (result_typed second) .nil)
  have outputType : Types.callOutput .chooseLonger [.adt .embedding, .adt .embedding] = some (.adt .embedding) := by
    simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
  have ready := Derived.call_ready_from_values (callers := callers) h.native.valid source typed outputType
  have machine := h.advance_call (Recursive.original_typed_respects 0 1) (Recursive.original_owns 0 1)
    .chooseLonger args root outside ready source safe closed (fun index member => Or.inl (family index member)) bounded
    (result_typed (OrderedSolver.selectResult first second)) (.adt .embedding) state execute
  have fresh := Derived.choice_call_owner_provenance 1 0 h.native.valid h.native.callersValid h.native.wellFormed
    h.native.ownerFrame h.native.coverage ready inputs execute
  have shape := Derived.call_shape execute
  refine ⟨final, after, machine, shape.2.2, shape.2.1, shape.1, state, fresh, ?_, ?_, ?_⟩
  · intro other otherBound notL notR notD above
    exact Derived.call_keeps_owner_provenance (Recursive.original_typed_respects 0 1)
      h.native.valid h.native.callersValid h.native.wellFormed ready otherBound
      (by simp [args, LocalPreservation.action, LocalPreservation.operands, LocalPreservation.operand, splitPlace, notL, notR, notD]) above execute
  · intro slot other notD bound cell read
    have kept := Derived.call_preserves_other_root (Recursive.original_typed_respects 0 1)
      h.native.valid h.native.callersValid h.native.wellFormed .chooseLonger args destination ready execute notD bound
    exact kept.reads other.address (by simp) cell read
  · intro fuel budget positive
    have same := Derived.call_callee_congr (Recursive.original budget fuel) (Recursive.original 0 1) .chooseLonger
      (Recursive.original_choice_callee_same budget fuel 0 1 positive (by decide)) world active callers args destination
    exact same.trans execute

end SubtreeProofs.Rust.SourceEval.Evaluator
