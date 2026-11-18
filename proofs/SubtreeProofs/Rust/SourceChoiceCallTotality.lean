module

public import SubtreeProofs.Rust.SourceRecursiveChoiceTotality
public import SubtreeProofs.Rust.SourceRecursiveHelperCallTotality
public import SubtreeProofs.Rust.SourceOwnerRecursive

/-! Whole actual recursive choice calls construct arguments, callee entry/body/
closure and the destination write. Transfer permission concerns only the chosen
argument owners and actual post-argument suspended loans, allowing unrelated
shared aliases. No successful parent/callee call or post-callee frame is an input. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

def ArgumentsLoansAllowed (world : World) (active : Activation) (callers : List Activation)
    (args : List Operand) (masks : State) : Prop :=
  ∀ guarded packets owners suspended,
    Addressed.operands world active.roots guarded active.state args = some (packets, masks) →
    FieldsFootprint world.memory (packets.map Prod.fst) owners →
    Callers world ({active with state := masks} :: callers) suspended → List.Disjoint owners suspended.loans

theorem packets_two_values {packets : List ValueCell} {first second : Value}
    (values : packets.map Prod.snd = [first, second]) :
    ∃ firstCell secondCell, packets = [(firstCell, first), (secondCell, second)] := by
  have length : packets.length = 2 := by
    have same := congrArg List.length values
    simpa only [List.length_map, List.length_cons, List.length_nil] using same
  cases packets with
  | nil => cases length
  | cons left rest => cases rest with
    | nil => cases length
    | cons right rest => cases rest with
      | cons _ _ => simp only [List.length_cons] at length; omega
      | nil =>
        rcases left with ⟨firstCell, firstValue⟩
        rcases right with ⟨secondCell, secondValue⟩
        simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at values
        obtain ⟨rfl, rfl⟩ := values
        exact ⟨firstCell, secondCell, rfl⟩

theorem choice_call_total (budget fuel : Nat) {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (args : List Operand) {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (first second : CommonEmbedding) {masks : State}
    (source : SourceEval.operands active.state args = some ([encodeResult first, encodeResult second], masks))
    (empty : masks slot = .empty)
    (moves : ∀ current suspended, Scanned world active current → Callers world callers suspended →
      ∀ op ∈ args, Allowed world active.roots (current.loans ++ suspended.reads) op)
    (loans : RootLoansAllowed world {active with state := masks} callers slot binding)
    (transferLoans : ArgumentsLoansAllowed world active callers args masks) :
    ∃ final after,
      call (Recursive.original budget (fuel + 1)) world active callers .chooseLonger args slot = some (final, after,
        (Cost.local (Action.call .chooseLonger args slot).weight).plus (Choice.cost first second)) ∧
      after.state = masks.set slot (Slot.ofValue (encodeResult (OrderedSolver.selectResult first second))) ∧
      SourceEval.action (SourceEval.run Certificate.original.body (fuel + 1)) active.state (.call .chooseLonger args slot) =
        some (after.state, (Cost.local (Action.call .chooseLonger args slot).weight).plus (Choice.cost first second)) ∧
      after.Valid final ∧ final.WellFormed ∧ (∀ caller ∈ callers, caller.Valid final) ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  obtain ⟨current, scan, scanned⟩ := active.scan_complete ha
  obtain ⟨suspended, callerScan, callerView⟩ := scanCallers_complete callers hc
  obtain ⟨packets, arguments, valuesEq⟩ := Addressed.operands_complete scanned.frame args source
    (moves current suspended scanned callerView)
  obtain ⟨_, _, graph, subset, middleFrame⟩ := Addressed.operands_spec scanned.frame args arguments
  let middle : Activation := {active with state := masks}
  have middleValid : middle.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨remainder, remainingScan, remaining, _⟩ := middle.context_complete middleValid slot
  obtain ⟨allResources, allScan, guardsCovered⟩ := middle.call_guards_covered middleValid remainingScan callerScan hb
  have suspendedValid : ∀ caller ∈ middle :: callers, caller.Valid world := by
    intro caller member
    rcases List.mem_cons.mp member with rfl | old
    · exact middleValid
    · exact hc caller old
  have allView := scanCallers_spec suspendedValid allScan
  have readable := packets_readable graph (fun address member => scanned.frame.alive address (subset member))
  obtain ⟨owners, footprint, partition⟩ := operands_owners ha args arguments
  have transfer : (active.owners world ++ (callerOwners world callers ++ external)).Perm
      (owners ++ (callerOwners world (middle :: callers) ++ external)) := by
    simpa only [middle, callerOwners, List.flatMap_cons, List.append_assoc] using
      partition.append_right (callerOwners world callers ++ external)
  have permitted := transferLoans (current.loans ++ suspended.reads) packets owners allResources arguments footprint allView
  obtain ⟨firstCell, secondCell, packetShape⟩ := packets_two_values valuesEq
  subst packets
  obtain ⟨returned, packet, execute, native, packetRead, returnedWf, kept, outputOwners,
    outputFootprint, outputFrame, _⟩ := Recursive.original_choice_total budget fuel hw suspendedValid first second firstCell secondCell
      (readable (firstCell, encodeResult first) (by simp)) (readable (secondCell, encodeResult second) (by simp))
      allView footprint (hf.perm transfer) (covered.perm transfer) permitted guardsCovered
  have retained := kept.weaken (fun _ member => List.mem_append_left _ member)
  have postValid := Activation.preserve_call_context middleValid hb empty remaining callerView kept
  have postRemaining := remaining.transport (retained.weaken (fun _ member => List.mem_append_left _ member))
  have postCallers := callerView.transport (retained.weaken (fun _ member => List.mem_append_right _ member))
  have postFrame : OwnerFrame returned (outputOwners ++ (middle.owners returned ++ (callerOwners returned callers ++ external))) := by
    simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using outputFrame
  have typedOutput : SnapshotTyped packet.2 (.adt .embedding) := by rw [native]; exact result_typed _
  have stored := store_complete postValid returnedWf separate hb empty packetRead outputFootprint postFrame
    postRemaining postCallers (StoreLoansAllowed.of_closed (loans.transport remaining callerView retained) typedOutput (.adt .embedding))
  have run := call_run scan callerScan arguments remainingScan hb execute stored
  have ready := call_ready_from_values (callers := callers) ha source
    (.cons (result_typed first) (.cons (result_typed second) .nil)) (function := .chooseLonger) (ty := .adt .embedding)
    (by simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output])
  have spec := call_spec (Recursive.original_typed_respects budget (fuel + 1)) ha hc hw .chooseLonger args slot ready run
  have resources := call_owner_resources (Recursive.original_typed_respects budget (fuel + 1))
    (Recursive.original_owns budget (fuel + 1)) ha hc hw .chooseLonger args slot hf covered ready run
  refine ⟨returned.write binding.address packet.1, {active with state := masks.set slot (Slot.ofValue packet.2)},
    run, ?_, spec.1, spec.2.2.2.2.1, spec.2.2.2.2.2.2.1, spec.2.2.2.2.2.1, resources⟩
  rw [native]

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
