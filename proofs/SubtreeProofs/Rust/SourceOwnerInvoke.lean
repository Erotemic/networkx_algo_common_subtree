module

public import SubtreeProofs.Rust.SourceOwnerControl
public import SubtreeProofs.Rust.SourceEvalGuardedEntry

/-! Actual parsed function entry, calling control, return extraction and checked
stack closure compose the complete caller/output owner invariant. These are
successful-execution contracts, separate from universal physical progress. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem invoke_owner_resources {callee : Derived.Callees} {source : Calls}
    (hcallee : CallsRespect callee source TypedReady) (howns : CallsOwn callee)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (hd : ReadyFor callee TypedReady callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  unfold invoke at h
  split at h
  next arity =>
    obtain ⟨henter, ha, hentered, hkept⟩ := enter_definition hw world.memory.length decl hp arity
    have entered := enter_owner_resources hw world.memory.length decl.source.localCount hc hp ho hf covered henter
    simp only [henter, Bind.bind, Option.bind] at h
    cases hr : exec callee callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets) with
    | none => simp [hr] at h
    | some result =>
      rcases result with ⟨flow, work⟩
      have hcallers : ∀ a ∈ callers, a.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
        intro a hm
        obtain ⟨bound, used, frame⟩ := hc a hm
        exact ⟨bound, used, frame.preserve (hkept used).preserves⟩
      have resources := exec_owner_resources hcallee howns ha hcallers hentered _ hd entered.1 entered.2 hr
      have valid := (exec_spec hcallee ha hcallers hentered _ hd hr).2.2.2
      cases flow with
      | next middle after => simp [hr] at h
      | returned middle after returned =>
        simp only [hr] at h
        cases hclose : close middle after callers guards returned with
        | none => simp [hclose] at h
        | some ending =>
          simp only [hclose, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨output, footprint, frame, coverage⟩ := resources
          exact ⟨output, close_owner_transfer valid.active valid.callers valid.wellFormed valid.packet
            footprint frame coverage hclose⟩
  next => cases h

theorem guardedInvoke_owner_resources {callee : Derived.Callees} {source : Calls}
    (hcallee : CallsRespect callee source TypedReady) (howns : CallsOwn callee)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (hf : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (hd : ReadyFor callee TypedReady callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : guardedInvoke callee callers guards decl world packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external)) := by
  unfold guardedInvoke at h
  cases hs : scanCallers world callers with
  | none => simp [hs] at h
  | some suspended =>
    simp only [hs, Bind.bind, Option.bind] at h
    split at h
    next => exact invoke_owner_resources hcallee howns decl hw hc hp ho hf covered hd h
    next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
