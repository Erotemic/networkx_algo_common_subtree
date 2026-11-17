module

public import SubtreeProofs.Rust.LookupBorrowCalls
public import SubtreeProofs.Rust.LookupBorrowOutputs
public import SubtreeProofs.Rust.LookupStackRefinement

/-! Retained source, recursive stable shared loans, reference-free results,
storage/frame/spatial safety and complete source currencies in one lookup run.
The interpreted memory remains immutable apart from fresh allocation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

theorem result_unborrowed {base current : Memory} {cell : Cell} {function : Function}
    (hext : Extends base current) (hf : function ≠ .boxNew)
    (h : Safe base current cell (SourceTypes.output function)) : Unborrowed current cell :=
  typed_unborrowed (h.typed hext) (ordinary_output_closed function hf)

theorem certified_run_loans (base : Memory) (fuel : Nat) (function : Function) (cells : List Cell)
    (types : List Ty) (values : List Value) (memory : Memory) (value : Value) (cost : Cost) (ty : Ty)
    (hext : Extends base memory) (hvalues : RepresentsFields memory cells values)
    (hargs : FieldsSafe base memory cells types) (ht : SourceTypes.callOutput function types = some ty)
    (hr : Control.run LookupSource.Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe base Program.body fuel function cells memory cell after cost ∧ Safe base after cell ty ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_run_spec fuel function memory cells values value cost hvalues hr
  obtain ⟨hsafe, _, htrace⟩ := original_safe base fuel function cells types memory cell after cost ty hext hargs ht he
  exact ⟨cell, after, he, htrace, hsafe, hv, hex, hlen⟩

theorem certified_mutant_loans (base : Memory) (fuel : Nat) (function : Function) (cells : List Cell)
    (types : List Ty) (values : List Value) (memory : Memory) (value : Value) (cost : Cost) (ty : Ty)
    (hext : Extends base memory) (hvalues : RepresentsFields memory cells values)
    (hargs : FieldsSafe base memory cells types) (ht : SourceTypes.callOutput function types = some ty)
    (hr : Control.run LookupSource.Certificate.mutant.body fuel function values = some (value, cost)) :
    ∃ cell after, Heap.run ExtraCompare.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe base ExtraCompare.body fuel function cells memory cell after cost ∧ Safe base after cell ty ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, he, hv, hex, hlen⟩ :=
    Heap.certified_mutant_spec fuel function memory cells values value cost hvalues hr
  obtain ⟨hsafe, _, htrace⟩ := mutant_safe base fuel function cells types memory cell after cost ty hext hargs ht he
  exact ⟨cell, after, he, htrace, hsafe, hv, hex, hlen⟩

theorem lookup_loans (fuel : Nat) (memory : Memory) (pt pl pr : Pointer)
    (ht : Typed memory (.shared pt) (.shared (.adt .table)))
    (hl : Typed memory (.shared pl) (.shared (.adt .word)))
    (hright : Typed memory (.shared pr) (.shared (.adt .word)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    RunSafe memory Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Safe memory after cell (.adt .optional) ∧ Unborrowed after cell ∧ Extends memory after := by
  have hargs : FieldsSafe memory memory [.shared pt, .shared pl, .shared pr] (SourceTypes.inputs .lookup) :=
    fields_from_base (.refl memory) (.cons ht (.cons hl (.cons hright .nil)))
  obtain ⟨hsafe, hext, htrace⟩ := original_safe memory fuel .lookup _ _ memory cell after cost (.adt .optional)
    (.refl memory) hargs (by simp [SourceTypes.callOutput, SourceTypes.sameList_refl, SourceTypes.output]) hr
  exact ⟨htrace, hsafe, result_unborrowed (function := .lookup) hext (by decide) hsafe, hext⟩

open verified_ordered_core in
theorem lookup_loan_total (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSafe memory Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Safe memory after cell (.adt .optional) ∧ Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .lookup [.shared pt, .shared pl, .shared pr]
        memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory cell after cost ∧
      Owns after cell memory.length after.length ∧
      Represents after cell (encodeOption (MemoizedOrderedSolver.findResult table left right)) ∧
      Typed after cell (.adt .optional) ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧
      cost.events = (LookupEvents.lookup table left right).2 ∧
      cost.steps ≤ 256 * cost.events.units ∧
      (∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hr, hstack, hspatial, hframe, howns, hv, ht, hext, hlen, hevents, hsteps, hprotected⟩ :=
    Stack.lookup_stack_total table left right fuel hf memory pt pl pr hTable hLeft hRight
  obtain ⟨htrace, hsafe, hclosed, _⟩ := lookup_loans fuel memory pt pl pr
    (hTable.typed (.shared (table_typed table))) (hLeft.typed (.shared (word_typed left)))
    (hRight.typed (.shared (word_typed right))) hr
  exact ⟨cell, after, cost, hr, htrace, hsafe, hclosed, hstack, hspatial, hframe, howns, hv, ht, hext,
    hlen, hevents, hsteps, hprotected, fun _ _ hl => hl.stable hext⟩

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
