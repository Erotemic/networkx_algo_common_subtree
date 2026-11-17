module

public import SubtreeProofs.Rust.LookupStackCertificate
public import SubtreeProofs.Rust.LookupSpatialRefinement

/-! Composition of retained source control, explicit normal storage states,
typed readback, intermediate owner separation and complete lookup currencies.
Borrow regions, physical stack layout and failed/unwind execution are separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Stack

open Heap

theorem certified_run_stack (fuel : Nat) (function : Function) (cells : List Cell)
    (values : List Value) (memory : Memory) (value : Value) (cost : Cost)
    (hvalues : RepresentsFields memory cells values) (hargs : cells.length = Frontend.arity function)
    (hr : Control.run LookupSource.Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe Certificate.original Certificate.originalCount fuel function cells memory cell after cost ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_run_spec fuel function memory cells values value cost hvalues hr
  exact ⟨cell, after, he, Certificate.original_run_safe fuel function cells memory hargs he, hv, hex, hlen⟩

open verified_ordered_core in
theorem lookup_stack_total (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSafe Certificate.original Certificate.originalCount fuel .lookup [.shared pt, .shared pl, .shared pr]
        memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Owns after cell memory.length after.length ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units ∧
      ∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hr, hspatial, hsafe, howns, hv, ht, hext, hlen, hevents, hsteps, hframe⟩ :=
    Spatial.lookup_spatial_total table left right fuel hf memory pt pl pr hTable hLeft hRight
  exact ⟨cell, after, cost, hr, Certificate.original_run_safe fuel .lookup _ memory rfl hr,
    hspatial, hsafe, howns, hv, ht, hext, hlen, hevents, hsteps, hframe⟩

end SubtreeProofs.Rust.LookupSource.Stack
