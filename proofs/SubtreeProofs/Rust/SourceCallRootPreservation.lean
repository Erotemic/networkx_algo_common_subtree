module

public import SubtreeProofs.Rust.SourceCallRetainedContext

/-! Whole calls retain every non-destination local root, including the raw
pointer bits of a moved reference. The actual remaining-context guards include
these roots even when their logical masks are empty. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem call_preserves_other_root {callee : Callees} {source : Calls} {ready : Ready}
    (respects : CallsRespect callee source ready)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (function : Function) (args : List Operand) (slot : Nat)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      ready world function packets)
    (run : call callee world active callers function args slot = some (final, after, cost))
    {other : Nat} {target : Binding} (different : other ≠ slot) (ht : active.roots other = some target) :
    Preserves world final [target.address] := by
  simp only [call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, hcurrent, suspended, hsuspended, ⟨packets, masks⟩, hargs,
    remainder, hrest, binding, hb, ⟨returned, packet, inner⟩, hcall,
    ⟨next, state⟩, hstore, last⟩ := run
  cases last
  have currentFrame := (Activation.scan_spec ha hcurrent).frame
  have callerFrame := scanCallers_spec hc hsuspended
  obtain ⟨used, _, graph, subset, middleFrame⟩ := Addressed.operands_spec currentFrame args hargs
  have middleValid : ({active with state := masks} : Activation).Valid world := ⟨ha.1, _, middleFrame⟩
  have context := Activation.context_spec middleValid slot hrest
  have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
    intro address member
    rcases List.mem_append.mp member with old | root
    · rcases List.mem_append.mp old with own | caller
      · exact context.alive address own
      · exact callerFrame.alive address caller
    · obtain ⟨_, _, _, _, _, included⟩ := middleFrame.get hb
      exact middleFrame.alive address (included (List.mem_append_right _ root))
  obtain ⟨_, readable, returnedWf, kept⟩ := respects world _ ({active with state := masks} :: callers)
    function packets returned packet inner hw
    (packets_readable graph (fun address member => currentFrame.alive address (subset member)))
    (by intro caller member; rcases List.mem_cons.mp member with rfl | old; exact middleValid; exact hc caller old)
    alive (hready current suspended packets masks hcurrent hsuspended hargs) hcall
  have retained := kept.weaken (fun _ member => List.mem_append_left _ member)
  have enlarged := context.weaken (fun _ member => List.mem_append_left _ member)
    (fun address member => alive address (List.mem_append_left _ member))
  have write := (store_spec returnedWf (enlarged.preserve retained) readable hstore).2.2.1
  have otherBinding : (active.roots.set slot none) other = some target := by
    simpa only [Roots.set, different, ite_false] using ht
  obtain ⟨_, _, _, _, _, included⟩ := context.get otherBinding
  apply (retained.trans write).weaken
  intro address member
  have same := List.mem_singleton.mp member
  subst address
  exact List.mem_append_left _ (included (List.mem_append_right _ (by simp)))

theorem source_call_state {call : Calls} {state masks after : State} {function : Function}
    {args : List Operand} {values : List Value} {slot : Nat} {cost : Cost}
    (source : SourceEval.operands state args = some (values, masks))
    (run : SourceEval.action call state (.call function args slot) = some (after, cost)) :
    ∃ value, after = masks.set slot (Slot.ofValue value) := by
  simp only [SourceEval.action, source, bind, Option.bind] at run
  cases child : call function values with
  | none => simp only [child] at run; cases run
  | some result =>
    rcases result with ⟨value, work⟩
    rw [child] at run
    exact ⟨value, (Prod.mk.inj (Option.some.inj run)).1.symm⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
