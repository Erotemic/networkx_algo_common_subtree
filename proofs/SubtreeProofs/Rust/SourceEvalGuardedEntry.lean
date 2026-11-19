module

public import SubtreeProofs.Rust.SourceEvalCallerPreservation

/-! A recursive entry checks that the supplied protected addresses belong to
its actual suspended caller inventory. Whole-body caller preservation then
establishes the callee contract on those addresses, including the destination. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def guardedInvoke (callee : Derived.Callees) (callers : List Activation) (guards : List Nat)
    (decl : TypeReader.Definition) (world : World) (packets : List ValueCell) : Option (World × ValueCell × Cost) := do
  let suspended ← scanCallers world callers
  if guards.all (fun address => decide (address ∈ suspended.reads)) then
    invoke callee callers guards decl world packets
  else none

theorem guardedInvoke_complete {callee : Derived.Callees} {callers : List Activation} {guards : List Nat}
    {decl : TypeReader.Definition} {world : World} {packets : List ValueCell} {suspended : Resources}
    (hs : scanCallers world callers = some suspended) (hg : guards ⊆ suspended.reads) :
    guardedInvoke callee callers guards decl world packets = invoke callee callers guards decl world packets := by
  have hall : guards.all (fun address => decide (address ∈ suspended.reads)) = true :=
    List.all_eq_true.mpr (fun _ hm => decide_eq_true (hg hm))
  simp only [guardedInvoke, hs, hall, Bind.bind, Option.bind, ite_true]

theorem guardedInvoke_spec {callee : Derived.Callees} {body : Function → Code} {fuel : Nat} {ready : Derived.Ready}
    (hcallee : Derived.CallsRespect callee (SourceEval.run body fuel) ready)
    (decl : TypeReader.Definition) (hcode : decl.source.code = body decl.source.function)
    (hnbox : decl.source.function ≠ .boxNew) (hnadd : decl.source.function ≠ .checkedAdd)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee ready callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : guardedInvoke callee callers guards decl world packets = some (final, packet, cost)) :
    SourceEval.run body (fuel + 1) decl.source.function (packets.map Prod.snd) = some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards := by
  unfold guardedInvoke at h
  cases hs : scanCallers world callers with
  | none => simp [hs] at h
  | some suspended =>
    simp only [hs, Bind.bind, Option.bind] at h
    split at h
    next accepted =>
      obtain ⟨hsource, hpacket, hfinal, _⟩ := invoke_run hcallee decl hcode hnbox hnadd hw hc hp hd h
      have kept := invoke_preserves hcallee decl hw hc hp hd h hs
      refine ⟨hsource, hpacket, hfinal, kept.weaken ?_⟩
      intro a ha
      exact of_decide_eq_true (List.all_eq_true.mp accepted a ha)
    next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
