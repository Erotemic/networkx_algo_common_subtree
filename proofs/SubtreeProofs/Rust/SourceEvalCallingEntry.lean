module

public import SubtreeProofs.Rust.SourceActivationClose
public import SubtreeProofs.Rust.SourceActivationInitial

/-! Execute an actual parsed declaration using fresh argument storage, calling
control and checked return cleanup. Entry costs and the complete body cost are
preserved. The recursive dispatch contract, native path readiness, whole-run
physical success and exclusive transfer remain explicit obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def invoke (callee : Derived.Callees) (callers : List Activation) (guards : List Nat)
    (decl : TypeReader.Definition) (world : World) (packets : List ValueCell) : Option (World × ValueCell × Cost) := do
  if packets.length = (Types.inputs decl.source.function).length then
    let (entered, active) ← enter world world.memory.length decl.source.localCount packets
    let (result, work) ← exec callee callers decl.source.code entered active
    match result with
    | .next _ _ => none
    | .returned middle after packet =>
      let final ← close middle after callers guards packet
      some (final, packet, (Cost.entry decl.source.function).plus work)
  else none

theorem invoke_spec {callee : Derived.Callees} {source : Calls} {ready : Derived.Ready}
    (hcallee : Derived.CallsRespect callee source ready)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee ready callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    packets.length = (Types.inputs decl.source.function).length ∧
      ∃ (work : Cost) (middle : World) (after : Activation),
        SourceEval.exec source decl.source.code (initialState (packets.map Prod.snd)) = some (.returned packet.2, work) ∧
        cost = (Cost.entry decl.source.function).plus work ∧
        final = middle.retire after.stackAddresses ∧ after.count = decl.source.localCount ∧
        final.memory = middle.memory ∧ final.classes = middle.classes ∧ final.WellFormed ∧
        Readable final.memory final.live packet.1 packet.2 ∧ (∀ a ∈ callers, a.Valid final) ∧
        (∀ slot, (after.state slot).dropWork.boxes = 0) ∧
        (∀ slot binding, after.roots slot = some binding → final.live binding.address = false) ∧
        (∀ address, middle.classes address = some .box → final.live address = middle.live address) := by
  unfold invoke at h
  split at h
  next arity =>
    obtain ⟨henter, ha, hentered, hkept⟩ := enter_definition hw world.memory.length decl hp arity
    simp only [henter, Bind.bind, Option.bind] at h
    cases hr : exec callee callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets) with
    | none => simp [hr] at h
    | some result =>
      rcases result with ⟨flow, work⟩
      have hcallers : ∀ a ∈ callers, a.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
        intro a hm
        obtain ⟨bound, used, hf⟩ := hc a hm
        exact ⟨bound, used, hf.preserve (hkept used).preserves⟩
      obtain ⟨hsource, _, hn, hv⟩ := exec_spec hcallee ha hcallers hentered _ hd hr
      cases flow with
      | next middle after => simp [hr] at h
      | returned middle after returned =>
        simp only [hr] at h
        cases hclose : close middle after callers guards returned with
        | none => simp [hclose] at h
        | some ending =>
          simp only [hclose, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨hfinal, hmemory, hclasses, hwf, hpacket, _, hz, hroots, hboxes, suspended, _, hcs, _⟩ :=
            close_spec hv.active hv.callers hv.wellFormed hv.packet hclose
          refine ⟨arity, work, middle, after, hsource, rfl, hfinal, hn, hmemory, hclasses, hwf, hpacket, ?_, hz, hroots, hboxes⟩
          intro a hm
          obtain ⟨_, hs, _, _, _⟩ := hcs.get hm
          exact hs.valid
  next => cases h

theorem invoke_run {callee : Derived.Callees} {body : Function → Code} {fuel : Nat} {ready : Derived.Ready}
    (hcallee : Derived.CallsRespect callee (SourceEval.run body fuel) ready)
    (decl : TypeReader.Definition) (hcode : decl.source.code = body decl.source.function)
    (hnbox : decl.source.function ≠ .boxNew) (hnadd : decl.source.function ≠ .checkedAdd)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee ready callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    SourceEval.run body (fuel + 1) decl.source.function (packets.map Prod.snd) = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ (∀ a ∈ callers, a.Valid final) := by
  obtain ⟨_, work, middle, after, hs, rfl, _, _, _, _, hwf, hp, hc, _⟩ := invoke_spec hcallee decl hw hc hp hd h
  rw [hcode] at hs
  refine ⟨?_, hp, hwf, hc⟩
  rw [Legacy.run_ordinary body fuel _ _ hnbox hnadd, hs]
  rfl

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
