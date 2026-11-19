module

public import SubtreeProofs.Rust.LookupFrameCalls
public import SubtreeProofs.Rust.LookupHeapReturnOwnership

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

theorem lookup_args (pt pl pr : Pointer) : ArgsMatch .lookup [.shared pt, .shared pl, .shared pr] :=
  ⟨rfl, Or.inr ⟨Plain.shared pt, Plain.shared pl, Plain.shared pr, trivial⟩⟩

theorem lookup_safe (fuel : Nat) (memory : Memory) (pt pl pr : Pointer)
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost :=
  original_run_safe fuel .lookup _ memory (lookup_args pt pl pr) hr

/-- The retained original source-control certificate and the frame checker
compose with the same complete execution/cost, not only its returned value. -/
theorem certified_run_safe (fuel : Nat) (function : Function) (cells : List Cell)
    (values : List Value) (memory : Memory) (value : Value) (cost : Cost)
    (hvalues : RepresentsFields memory cells values) (hargs : ArgsMatch function cells)
    (hr : Control.run Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe Program.body fuel function cells memory cell after cost ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_run_spec fuel function memory cells values value cost hvalues hr
  exact ⟨cell, after, he, original_run_safe fuel function cells memory hargs he, hv, hex, hlen⟩

open verified_ordered_core in
/-- Total native-input lookup with both intermediate frame safety and final
exclusive returned ownership. Neither property is substituted for the other. -/
theorem lookup_guarded (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Owns after cell memory.length after.length ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units := by
  obtain ⟨cell, after, cost, hr, hv, ht, hex, hlen, hevents, hb⟩ :=
    Heap.lookup_spec table left right memory _ (.cons hTable (.cons hLeft (.cons hRight .nil))) fuel hf
  exact ⟨cell, after, cost, hr, lookup_safe fuel memory pt pl pr hr,
    lookup_return_owns table left right fuel hf memory pt pl pr hTable hLeft hRight hr,
    hv, ht, hex, hlen, hevents, hb⟩

end SubtreeProofs.Rust.LookupSource.Heap.Frame
