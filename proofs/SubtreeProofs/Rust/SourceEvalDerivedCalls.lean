module

public import SubtreeProofs.Rust.SourceEvalHeapIntrinsics

/-! One-pass argument execution, local callee composition and guarded result
storage. Retained reads come from actual post-argument active/caller scans.
Readiness is an independent callee input/fuel condition, not a parent result. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

abbrev Callees := World → List Nat → Function → List ValueCell → Option (World × ValueCell × Cost)
abbrev Ready := World → Function → List ValueCell → Prop

def CallsRespect (concrete : Callees) (source : Calls) (ready : Ready) : Prop :=
  ∀ world guards function packets final packet cost,
    world.WellFormed → (∀ p ∈ packets, Readable world.memory world.live p.1 p.2) →
    AliveOn world.live guards → ready world function packets →
    concrete world guards function packets = some (final, packet, cost) →
    source function (packets.map Prod.snd) = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards

theorem packets_readable {world : World} {packets : List ValueCell} {reads : List Nat}
    (h : GraphFields world.memory (packets.map Prod.fst) (packets.map Prod.snd) reads)
    (hl : AliveOn world.live reads) : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
  induction packets generalizing reads with
  | nil => simp
  | cons head tail ih =>
    cases h with
    | @cons cell value cells values first rest hf hr =>
      intro p hp
      rcases List.mem_cons.mp hp with he | hm
      · subst p
        exact ⟨first, hf, fun a ha => hl a (List.mem_append_left _ ha)⟩
      · exact ih hr (fun a ha => hl a (List.mem_append_right _ ha)) p hm

theorem store_spec {world final : World} {roots : Roots} {frame slot : Nat} {retained : List Nat}
    {middle after : State} {packet : ValueCell} (hw : world.WellFormed)
    (context : Frame world frame (roots.set slot none) (middle.set slot .empty) retained)
    (hp : Readable world.memory world.live packet.1 packet.2)
    (h : store world roots frame slot retained middle packet = some (final, after)) :
    after = middle.set slot (Slot.ofValue packet.2) ∧
      (∃ guards, Frame final frame roots after guards) ∧ Preserves world final retained ∧ final.WellFormed := by
  rcases packet with ⟨cell, value⟩
  obtain ⟨used, hg, halive⟩ := hp
  unfold store at h
  by_cases hempty : emptySlot (middle slot) = true
  · cases hb : roots slot with
    | none => simp [hempty, hb] at h
    | some binding =>
      cases hs : world.writeStack frame slot binding (retained ++ used) cell with
      | none => simp [hempty, hb, hg.trace, hs] at h
      | some next =>
        simp only [hempty, hb, hg.trace, hs, Bind.bind, Option.bind, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hc, hl, _, hsep, rfl⟩ := World.writeStack_iff.mp hs
        have hf := Frame.store hw hb (emptySlot_iff _ |>.mp hempty) context hc hl hg.partial halive hsep
        exact ⟨rfl, ⟨_, hf.2.2⟩, world.write_preserves (fun hm => hsep (List.mem_append_left _ hm)) cell, hw.write _ _⟩
  · simp [hempty] at h

def call (callee : Callees) (world : World) (active : Activation) (callers : List Activation)
    (function : Function) (args : List Operand) (slot : Nat) : Option (World × Activation × Cost) := do
  let current ← active.scan world
  let suspended ← scanCallers world callers
  let (packets, masks) ← Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args
  let remainder ← ({ active with state := masks } : Activation).scanExcept world slot
  let binding ← active.roots slot
  let retained := remainder.reads ++ suspended.reads
  let (returned, packet, cost) ← callee world (retained ++ [binding.address]) function packets
  let (final, after) ← store returned active.roots active.frame slot retained masks packet
  some (final, { active with state := after }, (Cost.local (Action.call function args slot).weight).plus cost)

theorem call_spec {callee : Callees} {source : Calls} {ready : Ready}
    (hcallee : CallsRespect callee source ready)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (function : Function) (args : List Operand) (slot : Nat)
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      ready world function packets)
    (h : call callee world active callers function args slot = some (final, after, cost)) :
    SourceEval.action source active.state (.call function args slot) = some (after.state, cost) ∧
      after.frame = active.frame ∧ after.count = active.count ∧ after.roots = active.roots ∧
      after.Valid final ∧ (∀ a ∈ callers, a.Valid final) ∧ final.WellFormed ∧
      ∃ suspended, scanCallers world callers = some suspended ∧ Callers final callers suspended := by
  unfold call at h
  cases hcurrent : active.scan world with
  | none => simp [hcurrent] at h
  | some current =>
    cases hsuspended : scanCallers world callers with
    | none => simp [hcurrent, hsuspended] at h
    | some suspended =>
      cases hargs : Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args with
      | none => simp [hcurrent, hsuspended, hargs] at h
      | some pair =>
        rcases pair with ⟨packets, masks⟩
        cases hrest : ({ active with state := masks } : Activation).scanExcept world slot with
        | none => simp [hcurrent, hsuspended, hargs, hrest] at h
        | some remainder =>
          cases hb : active.roots slot with
          | none => simp [hcurrent, hsuspended, hb] at h
          | some binding =>
            simp only [hcurrent, hsuspended, hargs, hrest, hb, Bind.bind, Option.bind] at h
            cases hrun : callee world ((remainder.reads ++ suspended.reads) ++ [binding.address]) function packets with
            | none => simp only [hrun] at h; cases h
            | some returned =>
              rcases returned with ⟨returned, packet, inner⟩
              simp only [hrun] at h
              cases hstore : store returned active.roots active.frame slot (remainder.reads ++ suspended.reads) masks packet with
              | none => simp only [hstore] at h; cases h
              | some result =>
                rcases result with ⟨next, state⟩
                simp only [hstore,
                  Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have currentFrame := (Activation.scan_spec ha hcurrent).frame
                have callers := scanCallers_spec hc hsuspended
                obtain ⟨used, hsource, hg, hsub, hmid⟩ := Addressed.operands_spec currentFrame args hargs
                have hvalid : ({ active with state := masks } : Activation).Valid world := ⟨ha.1, _, hmid⟩
                have context := Activation.context_spec hvalid slot hrest
                have hlive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
                  intro a hm
                  rcases List.mem_append.mp hm with hm | hm
                  · rcases List.mem_append.mp hm with hm | hm
                    · exact context.alive a hm
                    · exact callers.alive a hm
                  · obtain ⟨_, _, _, _, _, covered⟩ := hmid.get hb
                    exact hmid.alive a (covered (List.mem_append_right _ hm))
                obtain ⟨hcallSource, hpacket, hreturned, hkept⟩ := hcallee world _ function packets returned packet inner hw
                  (packets_readable hg (fun a hm => currentFrame.alive a (hsub hm))) hlive
                  (hready current suspended packets masks hcurrent hsuspended hargs) hrun
                have hcontext := context.weaken (fun _ hm => List.mem_append_left _ hm) (by
                  intro a hm
                  exact hlive a (List.mem_append_left _ hm))
                have retained := hkept.weaken (fun _ hm => List.mem_append_left _ hm)
                have hcontext' := hcontext.preserve retained
                obtain ⟨hstate, ⟨guards, hframe⟩, hwrite, hfinal⟩ := store_spec hreturned hcontext' hpacket hstore
                have keepCallers := (retained.trans hwrite).weaken (fun _ hm => List.mem_append_right _ hm)
                have hcallers := callers.transport keepCallers
                refine ⟨?_, rfl, rfl, rfl, ⟨ha.1, guards, hframe⟩, ?_, hfinal, suspended, rfl, hcallers⟩
                · simp only [SourceEval.action, hsource, hcallSource, Bind.bind, Option.bind, hstate]
                · intro a hm
                  obtain ⟨_, hv, _, _, _⟩ := hcallers.get hm
                  exact hv.valid

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
