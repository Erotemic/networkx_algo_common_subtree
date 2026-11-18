module

public import SubtreeProofs.Rust.SourceEvalCallingEntry
public import SubtreeProofs.Rust.SourceEvalAddressedChoice

/-! The actual parsed choice declaration executes through the calling entry
path, preserving its established native tie rule and full cost, and closes all
remaining callee stack bindings. Physical success remains explicit. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

theorem invoking_refines (fuel budget : Nat) (decl : TypeReader.Definition)
    (hf : decl.source.function = .chooseLonger) (hcode : decl.source.code = body)
    {world final : World} {callers : List Activation} {guards : List Nat} {packets : List ValueCell}
    {packet : ValueCell} {cost : Cost} (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (first second : CommonEmbedding) (hi : packets.map Prod.snd = [encodeResult first, encodeResult second])
    (h : Calling.invoke (Helpers.callee fuel budget) callers guards decl world packets = some (final, packet, cost)) :
    packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧ cost = Choice.cost first second ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ (∀ a ∈ callers, a.Valid final) ∧
      ∃ (middle : World) (after : Activation), final = middle.retire after.stackAddresses ∧ after.count = decl.source.localCount ∧
        (∀ slot, (after.state slot).dropWork.boxes = 0) ∧
        (∀ slot binding, after.roots slot = some binding → final.live binding.address = false) ∧
        (∀ address, middle.classes address = some .box → final.live address = middle.live address) := by
  have hd := Calling.readyFor_noCalls (Helpers.callee fuel budget) (fun _ function packets => Helpers.Ready fuel function packets)
    callers body (by decide +kernel)
    (world.stackCells world.memory.length (packets.map Prod.fst))
    (initialActivation world world.memory.length decl.source.localCount packets)
  rw [← hcode] at hd
  obtain ⟨_, work, middle, after, hs, hcost, hfinal, hn, _, _, hwf, hpacket, hcallers, hz, hroots, hboxes⟩ :=
    Calling.invoke_spec (Helpers.callee_respects fuel budget) decl hw hc hp hd h
  rw [hcode, hi, body_exec] at hs
  obtain ⟨hvalue, hwork⟩ := Prod.mk.inj (Option.some.inj hs)
  have hvalue' := SourceEval.Outcome.returned.inj hvalue
  refine ⟨hvalue'.symm, ?_, hpacket, hwf, hcallers, middle, after, hfinal, hn, hz, hroots, hboxes⟩
  rw [hcost, ← hwork, hf]
  simp [Choice.cost, Cost.entry, Cost.plus, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus, entryEvents]
  omega

end SubtreeProofs.Rust.SourceEval.Choice
