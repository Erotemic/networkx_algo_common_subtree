module

public import SubtreeProofs.Rust.SourceNoCallOwnerLedger
public import SubtreeProofs.Rust.SourceOwnerInvoke

/-! Actual entry, primitive control, return extraction and stack closure retain
an output-owner subset of the supplied input inventory. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem invoke_noCalls_owner_ledger {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (owns : CallsOwn callee)
    (decl : TypeReader.Definition) (noncall : noCalls decl.source.code = true)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world)
    (readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (input : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (run : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧ output ⊆ owners := by
  unfold invoke at run
  split at run
  next arity =>
    obtain ⟨entryRun, valid, enteredWf, kept⟩ := enter_definition hw world.memory.length decl readable arity
    have entered := enter_owner_resources hw world.memory.length decl.source.localCount hc readable input frame covered entryRun
    simp only [entryRun, bind, Option.bind] at run
    cases bodyRun : exec callee callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets) with
    | none => simp [bodyRun] at run
    | some result =>
      rcases result with ⟨flow, work⟩
      have callersValid : ∀ caller ∈ callers, caller.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
        intro caller member
        obtain ⟨bounded, used, callerFrame⟩ := hc caller member
        exact ⟨bounded, used, callerFrame.preserve (kept used).preserves⟩
      have subset := exec_noCalls_owner_subset respects owns valid callersValid enteredWf _ noncall entered.1 entered.2 bodyRun
      have inputBound : packets.length + 1 ≤ decl.source.localCount := by
        have boundary := congrArg List.length decl.boundary
        have limited := List.length_take_le' ((Types.inputs decl.source.function).length + 1) decl.locals
        simp only [List.length_cons] at boundary
        rw [decl.count] at limited
        omega
      have initialOwners : (initialActivation world world.memory.length decl.source.localCount packets).owners
          (world.stackCells world.memory.length (packets.map Prod.fst)) = owners := by
        rw [initialActivation_owners _ _ readable inputBound, packetOwners_unique readable input]
      rw [initialOwners] at subset
      have ready := readyFor_noCalls callee TypedReady callers decl.source.code noncall
        (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets)
      have checked := (exec_spec respects valid callersValid enteredWf _ ready bodyRun).2.2.2
      cases flow with
      | next middle after => simp [bodyRun] at run
      | returned middle after returned =>
        simp only [bodyRun] at run
        cases closed : close middle after callers guards returned with
        | none => simp [closed] at run
        | some ending =>
          simp only [closed, Option.some.injEq, Prod.mk.injEq] at run
          obtain ⟨rfl, rfl, rfl⟩ := run
          obtain ⟨output, footprint, included⟩ := subset
          have memory : ending.memory = middle.memory := by
            simpa only [Flow.world] using (close_spec checked.active checked.callers checked.wellFormed checked.packet closed).2.1
          exact ⟨output, by simpa only [memory] using footprint,
            fun _ member => included (List.mem_append_left _ member)⟩
  next => cases run

theorem guardedInvoke_noCalls_owner_ledger {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (owns : CallsOwn callee)
    (decl : TypeReader.Definition) (noncall : noCalls decl.source.code = true)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost} {owners external : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world)
    (readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (input : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (run : guardedInvoke callee callers guards decl world packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧ output ⊆ owners := by
  unfold guardedInvoke at run
  cases scan : scanCallers world callers with
  | none => simp [scan] at run
  | some suspended =>
    simp only [scan, bind, Option.bind] at run
    split at run
    next => exact invoke_noCalls_owner_ledger respects owns decl noncall hw hc readable input frame covered run
    next => cases run

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
