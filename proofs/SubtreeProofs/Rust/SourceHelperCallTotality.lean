module

public import SubtreeProofs.Rust.SourceCallRetainedContext
public import SubtreeProofs.Rust.SourceEvalTypedRecursive
public import SubtreeProofs.Rust.SourceHelperFuel
public import SubtreeProofs.Rust.SourceMovePermissions

/-! Construct whole actual helper calls: execute arguments once, derive their
complete ownership and suspended frame, obtain sufficient stable helper bounds,
then construct the checked destination store. Local source argument steps and
move/root-loan permissions remain explicit; no successful call or post-callee
frame is supplied. Shared input aliases remain permitted. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem call_run {callee : Callees} {world returned final : World} {active : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {slot : Nat} {binding : Binding}
    {current suspended remainder : Resources} {packets : List ValueCell} {masks after : State}
    {packet : ValueCell} {cost : Cost}
    (scan : active.scan world = some current) (callerScan : scanCallers world callers = some suspended)
    (arguments : Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks))
    (remaining : ({active with state := masks} : Activation).scanExcept world slot = some remainder)
    (hb : active.roots slot = some binding)
    (execute : callee world ((remainder.reads ++ suspended.reads) ++ [binding.address])
      ({active with state := masks} :: callers) function packets = some (returned, packet, cost))
    (stored : store returned active.roots active.frame slot (remainder.reads ++ suspended.reads) masks packet = some (final, after)) :
    call callee world active callers function args slot =
      some (final, {active with state := after}, (Cost.local (Action.call function args slot).weight).plus cost) := by
  simp only [call, scan, callerScan, arguments, remaining, hb, execute, stored, bind, Option.bind]

theorem call_ready_from_values {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) {function : Function} {args : List Operand} {values : List Value} {masks : State}
    (source : SourceEval.operands active.state args = some (values, masks)) {types : List Ty} {ty : Ty}
    (typed : SnapshotFieldsTyped values types) (output : Types.callOutput function types = some ty) :
    ∀ current suspended packets middle, active.scan world = some current → scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, middle) →
      TypedReady world function packets := by
  intro current suspended packets middle scanned _ arguments
  obtain ⟨_, reflected, _, _, _⟩ := Addressed.operands_spec (Activation.scan_spec ha scanned).frame args arguments
  have same := (Prod.mk.inj (Option.some.inj (reflected.symm.trans source))).1
  exact ⟨types, ty, same ▸ typed, output⟩

theorem helper_call_stable {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (function : Function) (helper : Recursive.interpreted function = false) (args : List Operand)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    {values : List Value} {masks : State} (source : SourceEval.operands active.state args = some (values, masks))
    (empty : masks slot = .empty) {types : List Ty} {ty : Ty}
    (typed : SnapshotFieldsTyped values types) (outputType : Types.callOutput function types = some ty)
    (closed : Borrow.Closed ty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op)
    (loans : RootLoansAllowed world {active with state := masks} callers slot binding) :
    ∃ minimumFuel minimumBudget final after cost,
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        call (Helpers.callee fuel budget) world active callers function args slot = some (final, after, cost) ∧
        SourceEval.action (SourceEval.run Certificate.original.body fuel) active.state (.call function args slot) = some (after.state, cost) := by
  obtain ⟨current, scan, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, callerScan, callerView⟩ := scanCallers_complete callers hc
  obtain ⟨packets, arguments, valuesEq⟩ := Addressed.operands_complete scanned.frame args source
    (moves current suspended scanned callerView)
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec scanned.frame args arguments
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨remainder, remainingScan, remaining, context⟩ := middle.context_complete middleValid slot
  let guards := (remainder.reads ++ suspended.reads) ++ [binding.address]
  have guardsAlive : AliveOn world.live guards := by
    intro address member
    rcases List.mem_append.mp member with old | root
    · rcases List.mem_append.mp old with own | caller
      · exact remaining.alive address own
      · exact callerView.alive address caller
    · obtain ⟨_, _, _, _, _, included⟩ := middleFrame.get hb
      exact middleFrame.alive address (included (List.mem_append_right _ root))
  have readable := packets_readable graph (fun address member => scanned.frame.alive address (subset member))
  have suspendedValid : ∀ caller ∈ middle :: callers, caller.Valid world := by
    intro caller member
    rcases List.mem_cons.mp member with rfl | old
    · exact middleValid
    · exact hc caller old
  obtain ⟨owners, footprint, partition⟩ := operands_owners ha args arguments
  have transfer : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (owners ++ (callerOwners world (middle :: callers) ++ external)) := by
    simpa only [middle, callerOwners, List.flatMap_cons, List.append_assoc] using
      partition.append_right (callerOwners world callers ++ external)
  have packetTyped : SnapshotFieldsTyped (packets.map Prod.snd) types := valuesEq ▸ typed
  obtain ⟨minimumFuel, minimumBudget, returned, packet, inner, outputOwners, packetRead, returnedWf, kept,
    outputFootprint, outputFrame, outputCoverage, stable⟩ := Helpers.typed_owned_stable_bounds helper hw readable
      ⟨types, ty, packetTyped, outputType⟩ guards (middle :: callers) suspendedValid guardsAlive owners external
      footprint (hf.perm transfer) (covered.perm transfer)
  have typedOutput := Types.original_run_typed minimumFuel function _ types packet.2 inner ty packetTyped outputType
    (stable minimumFuel minimumBudget (Nat.le_refl _) (Nat.le_refl _)).2
  have retained := kept.weaken (fun _ member => List.mem_append_left _ member)
  have postValid := Activation.preserve_call_context middleValid hb empty remaining callerView kept
  have postRemaining := remaining.transport (retained.weaken (fun _ member => List.mem_append_left _ member))
  have postCallers := callerView.transport (retained.weaken (fun _ member => List.mem_append_right _ member))
  have postFrame : OwnerFrame returned (outputOwners ++ (middle.owners returned ++ (callerOwners returned callers ++ external))) := by
    simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using outputFrame
  have stored := store_complete postValid returnedWf separate hb empty packetRead outputFootprint postFrame
    postRemaining postCallers (StoreLoansAllowed.of_closed (loans.transport remaining callerView retained) typedOutput closed)
  have execute : ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
      call (Helpers.callee fuel budget) world active callers function args slot =
        some (returned.write binding.address packet.1, {active with state := masks.set slot (Slot.ofValue packet.2)},
          (Cost.local (Action.call function args slot).weight).plus inner) := by
    intro fuel budget fuelBound budgetBound
    exact call_run scan callerScan arguments remainingScan hb (stable fuel budget fuelBound budgetBound).1 stored
  have ready := call_ready_from_values (callers := callers) ha source typed outputType
  have first := execute minimumFuel minimumBudget (Nat.le_refl _) (Nat.le_refl _)
  have spec := call_spec (Helpers.callee_typed_respects minimumFuel minimumBudget) ha hc hw function args slot ready first
  have resources := call_owner_resources (Helpers.callee_typed_respects minimumFuel minimumBudget)
    (Helpers.callee_owns minimumFuel minimumBudget) ha hc hw function args slot hf covered ready first
  refine ⟨minimumFuel, minimumBudget, returned.write binding.address packet.1,
    {active with state := masks.set slot (Slot.ofValue packet.2)},
    (Cost.local (Action.call function args slot).weight).plus inner, spec.2.2.2.2.1, spec.2.2.2.2.2.2.1, spec.2.2.2.2.2.1,
    resources.1, resources.2, ?_⟩
  intro fuel budget fuelBound budgetBound
  have run := execute fuel budget fuelBound budgetBound
  exact ⟨run, (call_spec (Helpers.callee_typed_respects fuel budget) ha hc hw function args slot ready run).1⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
