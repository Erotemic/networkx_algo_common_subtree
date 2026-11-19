module

public import SubtreeProofs.Rust.LookupSpatialCalls
public import SubtreeProofs.Rust.LookupFrameRefinement

/-! Total native-input lookup with intermediate framed separation, normal
frame cleanup, independent readback/typing, final exclusive ownership and full
source costs. Immutable shared pointees do not transfer ownership. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Spatial

theorem lookup_profile (pt pl pr : Pointer) : Frame.ArgsMatch .lookup [.shared pt, .shared pl, .shared pr] :=
  ⟨rfl, Or.inr ⟨Frame.Plain.shared pt, ⟨Frame.Plain.shared pl, ⟨Frame.Plain.shared pr, trivial⟩⟩⟩⟩

theorem lookup_spatial (fuel : Nat) (memory : Memory) (pt pl pr : Pointer)
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    RunSpatial Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      ∀ frame, Separated memory frame → Separated after (cell :: frame) ∧ Extends memory after := by
  obtain ⟨hg, hp⟩ := original_spatial fuel .lookup _ memory cell after cost (lookup_profile pt pl pr) hr
  refine ⟨hg, fun frame hs => hp frame ?_⟩
  exact (Separated.plain_fields (.cons (.shared pt) (.cons (.shared pl) (.cons (.shared pr) .nil)))).mpr hs

open verified_ordered_core in
theorem lookup_spatial_total (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSpatial Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Owns after cell memory.length after.length ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units ∧
      ∀ frame, Separated memory frame → Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hr, hsafe, howns, hv, ht, hext, hlen, hevents, hsteps⟩ :=
    Frame.lookup_guarded table left right fuel hf memory pt pl pr hTable hLeft hRight
  obtain ⟨hspatial, hframe⟩ := lookup_spatial fuel memory pt pl pr hr
  exact ⟨cell, after, cost, hr, hspatial, hsafe, howns, hv, ht, hext, hlen, hevents, hsteps,
    fun frame hs => (hframe frame hs).1⟩

end SubtreeProofs.Rust.LookupSource.Heap.Spatial
