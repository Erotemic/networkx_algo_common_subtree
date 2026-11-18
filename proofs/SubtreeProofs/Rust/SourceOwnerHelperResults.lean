module

public import SubtreeProofs.Rust.SourceOwnerFresh
public import SubtreeProofs.Rust.SourceEvalHelperReflection
public import SubtreeProofs.Rust.SourceEvalTypedCalling

/-! Complete output ownership for successful actual helpers. The generic old
lookup/memo driver ledgers retain all transferred arguments and fresh Boxes;
output metadata is the actual readback packet. Native depth bounds are absent. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Heap.Owners Partial Partial.Addressed Storage

theorem finish_owner_ledger {budget : Nat} {world final : World}
    {raw : Option (Cell × Memory × LookupSource.Cost)} {cell : Cell} {memory : Memory}
    {oldCost : LookupSource.Cost} {packet : ValueCell} {cost : Cost} {packets : List ValueCell} {owners : List Nat}
    (hw : world.WellFormed) (hr : raw = some (cell, memory, oldCost))
    (hg : Grows world.memory memory (packets.map Prod.fst) [cell])
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    (h : finish budget world raw = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  obtain ⟨he, hc, _, _, _, _⟩ := finish_spec hw hr hg.memory h
  obtain ⟨a, ha, hp⟩ := hg.ledger owners ho
  obtain ⟨first, rest, rfl, hf, ht⟩ := ha.cons_inv
  cases ht
  refine ⟨first, ?_, ?_, ?_, ?_⟩
  · simpa only [he, hc, World.boxSuffix] using hf
  · simpa only [he, World.boxSuffix, List.append_nil] using hp
  · simpa only [he, World.boxSuffix] using hg.memory
  · rw [he]
    rfl

theorem lookup_owner_ledger (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : LookupSource.Function) (packets : List ValueCell)
    (profile : Heap.Frame.ArgsMatch function (packets.map Prod.fst)) {owners : List Nat}
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners) {packet : ValueCell} {cost : Cost}
    (h : lookup fuel budget world function packets = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  cases hr : Heap.run LookupSource.Program.body fuel function (packets.map Prod.fst) world.memory with
  | none => simp [lookup, finish, hr] at h
  | some raw =>
    rcases raw with ⟨cell, memory, work⟩
    have hg := lookup_grows fuel function _ _ cell memory work profile hr
    exact finish_owner_ledger hw hr hg ho h

theorem memo_owner_ledger (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : MemoSource.Function) (packets : List ValueCell)
    (profile : MemoSource.Frame.ArgsMatch function (packets.map Prod.fst)) {owners : List Nat}
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners) {packet : ValueCell} {cost : Cost}
    (h : memo fuel budget world function packets = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  cases hr : MemoSource.Heap.run MemoSource.Program.body fuel function (packets.map Prod.fst) world.memory with
  | none => simp [memo, finish, hr] at h
  | some raw =>
    rcases raw with ⟨cell, memory, work⟩
    have hg := MemoSource.Heap.run_grows fuel function _ _ cell memory work profile hr
    exact finish_owner_ledger hw hr hg ho h

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
