module

public import SubtreeProofs.Rust.LookupRegionCalls
public import SubtreeProofs.Rust.LookupRegionCertificate
public import SubtreeProofs.Rust.LookupBorrowRefinement

/-! Scoped retained-source programs and region-bearing runtime witnesses,
composed with unchanged lookup readback, ownership and operation currencies.
The region interpretation is the explicit immutable retained-world model. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions

theorem original_program : ∃ program, Reader.read Input.Program.source = .ok program ∧ Valid program Program.body :=
  Reader.check_sound Certificate.original_checked

theorem mutant_program : ∃ program, Reader.read Input.ExtraCompare.source = .ok program ∧ Valid program ExtraCompare.body :=
  Reader.check_sound Certificate.mutant_checked

theorem source_run_scoped (base : Memory) (fuel : Nat) (function : Function) (cells : List Cell)
    (types : List Heap.Ty) (values : List LookupSource.Value) (memory : Memory) (value : LookupSource.Value) (cost : Cost) (ty : Heap.Ty)
    (hext : Extends base memory) (hvalues : RepresentsFields memory cells values)
    (hargs : Borrow.FieldsSafe base memory cells types) (ht : SourceTypes.callOutput function types = some ty)
    (hr : Control.run LookupSource.Certificate.original.body fuel function values = some (value, cost)) :
    ∃ program, Reader.read Input.Program.source = .ok program ∧ ∃ cell after,
      Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunScoped base program Program.body fuel function cells memory cell after cost ∧
      Borrow.Safe base after cell ty ∧ Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨program, hread, hb⟩ := original_program
  obtain ⟨cell, after, hrun, hv, hex, hlen⟩ := Heap.certified_run_spec fuel function memory cells values value cost hvalues hr
  obtain ⟨hs, _, hscoped⟩ := run_scoped base program Program.body hb fuel function cells types memory cell after cost ty hext hargs ht hrun
  exact ⟨program, hread, cell, after, hrun, hscoped, hs, hv, hex, hlen⟩

theorem lookup_regions (fuel : Nat) (memory : Memory) (pt pl pr : Pointer)
    (ht : Typed memory (.shared pt) (.shared (.adt .table)))
    (hl : Typed memory (.shared pl) (.shared (.adt .word)))
    (hright : Typed memory (.shared pr) (.shared (.adt .word)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    ∃ program, Reader.read Input.Program.source = .ok program ∧
      RunScoped memory program Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost := by
  obtain ⟨program, hread, hb⟩ := original_program
  have hargs : Borrow.FieldsSafe memory memory [.shared pt, .shared pl, .shared pr] (SourceTypes.inputs .lookup) :=
    Borrow.fields_from_base (.refl memory) (.cons ht (.cons hl (.cons hright .nil)))
  have hs := (run_scoped memory program Program.body hb fuel .lookup _ _ memory cell after cost (.adt .optional)
    (.refl memory) hargs (by simp [SourceTypes.callOutput, SourceTypes.sameList_refl, SourceTypes.output]) hr).2.2
  exact ⟨program, hread, hs⟩

open verified_ordered_core in
theorem lookup_source_total (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ program, Reader.read Input.Program.source = .ok program ∧ ∃ cell after cost,
      Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunScoped memory program Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Borrow.RunSafe memory Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Borrow.Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .lookup [.shared pt, .shared pl, .shared pr]
        memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Owns after cell memory.length after.length ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧ cost.steps ≤ 256 * cost.events.units ∧
      (∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Borrow.Loan memory pointer ty → ∃ target, read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hr, hloan, _, hclosed, hstack, hspatial, hframe, howns, hv, ht, hext, hlen, hevents, hsteps, hprotected, hstable⟩ :=
    Borrow.lookup_loan_total table left right fuel hf memory pt pl pr hTable hLeft hRight
  obtain ⟨program, hread, hregions⟩ := lookup_regions fuel memory pt pl pr
    (hTable.typed (.shared (table_typed table))) (hLeft.typed (.shared (word_typed left)))
    (hRight.typed (.shared (word_typed right))) hr
  exact ⟨program, hread, cell, after, cost, hr, hregions, hloan, hclosed, hstack, hspatial, hframe, howns,
    hv, ht, hext, hlen, hevents, hsteps, hprotected, hstable⟩

end SubtreeProofs.Rust.LookupSource.Heap.Regions
