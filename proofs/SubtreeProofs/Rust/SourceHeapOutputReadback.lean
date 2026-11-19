module

public import SubtreeProofs.Rust.SourceEvalHeapHelpers

/-! Ordinary unborrowed helper outputs have identical read and owner graphs.
Their liveness follows from existing fresh/transfer ownership contracts, so
concrete metadata readback needs no assumed output-liveness postcondition. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem Graph.footprint {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
      (h : Graph memory cell value reads) (hu : Borrow.Unborrowed memory cell) : Footprint memory cell reads := by
    cases h with
    | boolean b => exact .boolean b
    | number n => exact .number n
    | node fields => cases hu with | node children => exact .node (fields.footprint children)
    | shared _ _ => cases hu
    | owned hr child => cases hu with
      | owned hs children =>
        have he := Option.some.inj (hr.symm.trans hs)
        cases he
        exact .owned hr (child.footprint children)

  theorem GraphFields.footprint {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
      (h : GraphFields memory cells values reads) (hu : Borrow.UnborrowedFields memory cells) :
      FieldsFootprint memory cells reads := by
    cases h with
    | nil => exact .nil
    | cons first rest => cases hu with
      | cons head tail => exact .cons (first.footprint head) (rest.footprint tail)
end

theorem readable_of_footprint {memory : Memory} {live : Live} {cell : Cell} {value : Value} {owners : List Nat}
    (hr : Represents memory cell value) (hu : Borrow.Unborrowed memory cell) (ho : Footprint memory cell owners)
    (hl : AliveOn live owners) : Readable memory live cell value := by
  obtain ⟨reads, hg⟩ := graph_of_represents hr
  have he : reads = owners := Rep.unique (Rep.of_full hr (hg.footprint hu)) (Rep.of_full hr ho)
  exact ⟨reads, hg, by simpa only [he] using hl⟩

theorem readable_owners {memory : Memory} {live : Live} {cell : Cell} {value : Value}
    (h : Readable memory live cell value) : ∃ owners, Footprint memory cell owners ∧ AliveOn live owners := by
  obtain ⟨reads, hg, hl⟩ := h
  obtain ⟨r, _, he, hv⟩ := hg.partial.resources
  refine ⟨r.owners, (hv.owned.materialize (Slot.materialize_ofValue value)).2, ?_⟩
  intro a ha
  exact hl a (he ▸ hv.owners_subset_reads ha)

namespace Storage

theorem World.boxSuffix_fresh_alive (world : World) (memory : Memory) :
    AliveOn (world.boxSuffix memory).live (List.range' world.memory.length (memory.length - world.memory.length)) := by
  intro a ha
  have hb := List.mem_range'_1.mp ha
  exact (world.boxSuffix_fresh memory hb.1 (by omega)).2

theorem World.boxSuffix_transfer_alive {world : World} (hw : world.WellFormed) {memory : Memory}
    (he : Extends world.memory memory) {old owners : List Nat} (hl : AliveOn world.live old)
    (hp : owners.Perm (old ++ List.range' world.memory.length (memory.length - world.memory.length))) :
    AliveOn (world.boxSuffix memory).live owners := by
  intro a ha
  rcases List.mem_append.mp (hp.subset ha) with ha | ha
  · exact (world.boxSuffix_keeps hw he old).alive a ha (hl a ha)
  · exact world.boxSuffix_fresh_alive memory a ha

theorem readable_fresh {world : World} {memory : Memory} {cell : Cell} {value : Value}
    (hr : Represents memory cell value) (hu : Borrow.Unborrowed memory cell)
    (ho : Owns memory cell world.memory.length memory.length) :
    Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell value :=
  readable_of_footprint hr hu ho.footprint (world.boxSuffix_fresh_alive memory)

theorem readable_transfer {world : World} (hw : world.WellFormed) {memory : Memory} (he : Extends world.memory memory)
    {cell : Cell} {value : Value} {old owners : List Nat}
    (hr : Represents memory cell value) (hu : Borrow.Unborrowed memory cell) (ho : Footprint memory cell owners)
    (hl : AliveOn world.live old)
    (hp : owners.Perm (old ++ List.range' world.memory.length (memory.length - world.memory.length))) :
    Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell value :=
  readable_of_footprint hr hu ho (World.boxSuffix_transfer_alive hw he hl hp)

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
