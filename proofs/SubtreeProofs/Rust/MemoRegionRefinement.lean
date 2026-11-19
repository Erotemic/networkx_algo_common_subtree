module

public import SubtreeProofs.Rust.MemoRegionCalls
public import SubtreeProofs.Rust.MemoBorrowRefinement

/-! Actual source-region annotations interpreted in retained heap worlds,
composed with memo native totality, stable loans and complete safety/cost traces. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Regions

open LookupSource LookupSource.Heap LookupSource.Heap.Borrow LookupSource.Heap.Regions verified_ordered_core

theorem source_run_scoped (base : Memory) (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (types : List Heap.Ty) (values : List LookupSource.Value) (value : LookupSource.Value) (cost : Cost) (ty : Heap.Ty)
    (hext : Extends base memory) (hrep : RepresentsFields memory cells values)
    (hargs : FieldsSafe base memory cells types) (ht : Types.callOutput function types = some ty)
    (hr : sourceRun MemoSource.Certificate.original.body fuel function values = some (value, cost)) :
    ∃ program, read Input.Program.source = .ok program ∧ ∃ cell after,
      MemoSource.Heap.run MemoSource.Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunScoped base program MemoSource.Program.body fuel function cells memory cell after cost ∧ Safe base after cell ty ∧
      Represents after cell value ∧ Extends memory after ∧ after.length = memory.length + cost.events.allocations := by
  obtain ⟨program, hread, hb⟩ := original_program_valid
  obtain ⟨cell, after, hrun, hv, hex, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hrep hr
  obtain ⟨hs, _, hscoped⟩ := run_scoped base program MemoSource.Program.body hb fuel function cells types memory cell after cost ty hext hargs ht hrun
  exact ⟨program, hread, cell, after, hrun, hscoped, hs, hv, hex, hlen⟩

theorem ordinary_regions (fuel : Nat) (function : Function) (hf : function ≠ .boxNew)
    (memory : Memory) (cells : List Cell) (hargs : FieldsTyped memory cells (Types.inputs function))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run MemoSource.Program.body fuel function cells memory = some (cell, after, cost)) :
    ∃ program, read Input.Program.source = .ok program ∧
      RunScoped memory program MemoSource.Program.body fuel function cells memory cell after cost := by
  obtain ⟨program, hread, hb⟩ := original_program_valid
  have hi := fields_from_base (Extends.refl memory) hargs
  have ht : Types.callOutput function (Types.inputs function) = some (Types.output function) := by
    simp only [Types.callOutput, hf, ite_false, SourceTypes.sameList_refl, ite_true]
  have hp := (run_scoped memory program MemoSource.Program.body hb fuel function cells _ memory cell after cost _
    (.refl memory) hi ht hr).2.2
  exact ⟨program, hread, hp⟩

theorem concatenate_source_total (left right : BalancedWord) (fuel : Nat) (hf : concatenateDepth left right ≤ fuel)
    (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ program, read Input.Program.source = .ok program ∧ ∃ cell after cost,
      sourceRun MemoSource.Certificate.original.body fuel .concatenate [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      MemoSource.Heap.run MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunScoped memory program MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Borrow.RunSafe memory MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Safe memory after cell (.adt .word) ∧ Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Spatial.RunSpatial MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe MemoSource.Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      (∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, LookupSource.Heap.read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hsource, hrun, hloan, hsafe, hclosed, hstack, hs, hg, hv, ht, ho, hex, hlen, he, hn, hframe, hstable⟩ :=
    Borrow.concatenate_loan_total left right fuel hf memory pl pr hLeft hRight
  obtain ⟨program, hread, hregions⟩ := ordinary_regions fuel .concatenate (by decide) memory _
    (.cons (hLeft.typed (.shared (word_typed left))) (.cons (hRight.typed (.shared (word_typed right))) .nil)) hrun
  exact ⟨program, hread, cell, after, cost, hsource, hrun, hregions, hloan, hsafe, hclosed, hstack, hs, hg,
    hv, ht, ho, hex, hlen, he, hn, hframe, hstable⟩

theorem insert_source_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ program, read Input.Program.source = .ok program ∧ ∃ cell after cost,
      sourceRun MemoSource.Certificate.original.body fuel .insert
          [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      MemoSource.Heap.run MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost) ∧
      RunScoped memory program MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Borrow.RunSafe memory MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Safe memory after cell (.adt .table) ∧ Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Spatial.RunSpatial MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Frame.RunSafe MemoSource.Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      (∀ frame, Spatial.Separated memory (tc :: frame) → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, LookupSource.Heap.read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hsource, hrun, hloan, hsafe, hclosed, hstack, hs, hg, hv, ht, hex, hlen, he, hn, htail, hframe, hstable⟩ :=
    Borrow.insert_loan_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  obtain ⟨program, hread, hregions⟩ := ordinary_regions fuel .insert (by decide) memory _
    (.cons (hTable.typed (table_typed table)) (.cons (hLeft.typed (.shared (word_typed left)))
      (.cons (hRight.typed (.shared (word_typed right))) (.cons (hResult.typed (.shared (result_typed result))) .nil)))) hrun
  exact ⟨program, hread, cell, after, cost, hsource, hrun, hregions, hloan, hsafe, hclosed, hstack, hs, hg,
    hv, ht, hex, hlen, he, hn, htail, hframe, hstable⟩

end SubtreeProofs.Rust.MemoSource.Regions
