module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins
public import SubtreeProofs.Rust.SourceCallRootPreservation

/-! Actual calls and assignments preserve an untouched query's complete local
inventory, including transitive referent reads. Source-local argument/RHS masks
identify an untouched query; the existing physical guards supply preservation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem assign_preserves_other_local {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {slot other : Nat} {rhs : Expr} {value : Value} {masks : State} {r : Resources}
    (source : SourceEval.expression active.state rhs = some (value, masks))
    (same : masks other = active.state other) (different : other ≠ slot) (bound : other < active.count)
    (represented : LocalResources world active.frame active.roots active.state other r)
    (run : assign world active callers slot rhs = some (final, after)) :
    Preserves world final r.reads ∧ after.frame = active.frame ∧ after.roots = active.roots ∧
      after.state other = active.state other := by
  simp only [assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, hcurrent, suspended, hsuspended, ⟨packet, middle⟩, he,
    remainder, hrest, ⟨next, state⟩, stored, last⟩ := run
  cases last
  have scanned := Activation.scan_spec ha hcurrent
  have callerView := scanCallers_spec hc hsuspended
  obtain ⟨_, reflected, _, _, middleFrame⟩ := Addressed.expression_spec scanned.frame he
  have actualSame : middle other = active.state other :=
    (congrArg (fun pair : Value × State => pair.2 other) (Option.some.inj (reflected.symm.trans source))).trans same
  let mid : Activation := {active with state := middle}
  have midValid : mid.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨actual, scan, remaining, context⟩ := mid.context_complete midValid slot
  have eq : actual = remainder := Option.some.inj (scan.symm.trans hrest)
  subst actual
  obtain ⟨item, itemRep, included, _, _⟩ := remaining.get (slot := other) (by change other ∈ remainingSlots active.count slot; simp [remainingSlots, bound, different])
  have query := represented.congr_at (nextState := middle) rfl actualSame
  have resourceEq : r = item := query.unique itemRep
  have protectedReads : r.reads ⊆ remainder.reads := by rw [resourceEq]; exact included
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member) (by
    intro address member
    rcases List.mem_append.mp member with own | old
    · exact context.alive address own
    · exact callerView.alive address old)
  have packetRead := (Addressed.expression_readable scanned.frame he).2.1
  have spec := store_spec hw enlarged packetRead stored
  refine ⟨spec.2.2.1.weaken (fun _ member => List.mem_append_left _ (protectedReads member)), rfl, rfl, ?_⟩
  rw [spec.1]
  simpa only [Partial.Locals.set, different, ite_false] using actualSame

theorem call_preserves_other_local {callee : Callees} {sourceCall : Calls} {ready : Ready}
    (respects : CallsRespect callee sourceCall ready)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (function : Function) (args : List Operand) (slot : Nat)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      ready world function packets)
    {values : List Value} {masks : State} (source : SourceEval.operands active.state args = some (values, masks))
    {other : Nat} {r : Resources} (same : masks other = active.state other) (different : other ≠ slot)
    (bound : other < active.count) (represented : LocalResources world active.frame active.roots active.state other r)
    (run : call callee world active callers function args slot = some (final, after, cost)) :
    Preserves world final r.reads := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, hcurrent, suspended, hsuspended, ⟨packets, middle⟩, hargs,
    remainder, hrest, binding, hb, ⟨returned, packet, inner⟩, hcall,
    ⟨next, state⟩, hstore, last⟩ := run
  cases last
  have currentFrame := (Activation.scan_spec ha hcurrent).frame
  have callerFrame := scanCallers_spec hc hsuspended
  obtain ⟨used, reflected, graph, subset, middleFrame⟩ := Addressed.operands_spec currentFrame args hargs
  have actualSame : middle other = active.state other :=
    (congrArg (fun pair : List Value × State => pair.2 other) (Option.some.inj (reflected.symm.trans source))).trans same
  let mid : Activation := {active with state := middle}
  have middleValid : mid.Valid world := ⟨ha.1, _, middleFrame⟩
  obtain ⟨actual, scan, remaining, context⟩ := mid.context_complete middleValid slot
  have eq : actual = remainder := Option.some.inj (scan.symm.trans hrest)
  subst actual
  have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
    intro address member
    rcases List.mem_append.mp member with old | root
    · rcases List.mem_append.mp old with own | caller
      · exact context.alive address own
      · exact callerFrame.alive address caller
    · obtain ⟨_, _, _, _, _, included⟩ := middleFrame.get hb
      exact middleFrame.alive address (included (List.mem_append_right _ root))
  obtain ⟨_, readable, returnedWf, kept⟩ := respects world _ (mid :: callers)
    function packets returned packet inner hw
    (packets_readable graph (fun address member => currentFrame.alive address (subset member)))
    (by intro caller member; rcases List.mem_cons.mp member with rfl | old; exact middleValid; exact hc caller old)
    alive (hready current suspended packets middle hcurrent hsuspended hargs) hcall
  have retained := kept.weaken (fun _ member => List.mem_append_left _ member)
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member)
    (fun address member => alive address (List.mem_append_left _ member))
  have write := (store_spec returnedWf (enlarged.preserve retained) readable hstore).2.2.1
  obtain ⟨item, itemRep, included, _, _⟩ := remaining.get (slot := other) (by change other ∈ remainingSlots active.count slot; simp [remainingSlots, bound, different])
  have query := represented.congr_at (nextState := middle) rfl actualSame
  have resourceEq : r = item := query.unique itemRep
  apply (retained.trans write).weaken
  intro address member
  exact List.mem_append_left _ (included (resourceEq ▸ member))

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
