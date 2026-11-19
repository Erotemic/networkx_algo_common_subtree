module

public import SubtreeProofs.Rust.MemoBorrowCalls
public import SubtreeProofs.Rust.MemoTypeRefinement
public import SubtreeProofs.Rust.MemoStackRefinement

/-! Actual memo typed shared-loan traces, ordinary borrow-free results and
retained caller loans composed with source/heap, storage and ownership costs. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Borrow

open LookupSource LookupSource.Heap LookupSource.Heap.Borrow verified_ordered_core

theorem result_unborrowed {base current : Memory} {cell : Cell} {function : Function}
    (hext : Extends base current) (hf : function ≠ .boxNew)
    (h : Safe base current cell (Types.output function)) : Unborrowed current cell :=
  typed_unborrowed (h.typed hext) (Types.ordinary_output_closed function hf)

theorem source_run_loans (base : Memory) (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (types : List Ty) (values : List Value) (value : Value) (cost : Cost) (ty : Ty)
    (hext : Extends base memory) (hrep : RepresentsFields memory cells values)
    (hargs : FieldsSafe base memory cells types) (ht : Types.callOutput function types = some ty)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe base Program.body fuel function cells memory cell after cost ∧ Safe base after cell ty ∧
      Represents after cell value ∧ Extends memory after ∧ after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, hrun, hv, hex, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hrep hr
  obtain ⟨hs, _, htrace⟩ := original_safe base fuel function cells types memory cell after cost ty hext hargs ht hrun
  exact ⟨cell, after, hrun, htrace, hs, hv, hex, hlen⟩

theorem ordinary_loans (fuel : Nat) (function : Function) (hf : function ≠ .boxNew)
    (memory : Memory) (cells : List Cell) (hargs : FieldsTyped memory cells (Types.inputs function))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost)) :
    RunSafe memory Program.body fuel function cells memory cell after cost ∧
      Safe memory after cell (Types.output function) ∧ Unborrowed after cell ∧ Extends memory after := by
  have hi := fields_from_base (Extends.refl memory) hargs
  have ht : Types.callOutput function (Types.inputs function) = some (Types.output function) := by
    simp only [Types.callOutput, hf, ite_false, SourceTypes.sameList_refl, ite_true]
  obtain ⟨hs, hex, htrace⟩ := original_safe memory fuel function cells _ memory cell after cost _ (.refl memory) hi ht hr
  exact ⟨htrace, hs, result_unborrowed hex hf hs, hex⟩

theorem concatenate_loan_total (left right : BalancedWord) (fuel : Nat) (hf : concatenateDepth left right ≤ fuel)
    (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      sourceRun MemoSource.Certificate.original.body fuel .concatenate [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      MemoSource.Heap.run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSafe memory Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Safe memory after cell (.adt .word) ∧ Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      (∀ frame, Spatial.Separated memory frame → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hsource, hrun, hstack, hs, hg, hv, ht, ho, hex, hlen, he, hn, hframe⟩ :=
    Stack.concatenate_stack_total left right fuel hf memory pl pr hLeft hRight
  obtain ⟨htrace, hsafe, hclosed, _⟩ := ordinary_loans fuel .concatenate (by decide) memory _
    (.cons (hLeft.typed (.shared (word_typed left))) (.cons (hRight.typed (.shared (word_typed right))) .nil)) hrun
  exact ⟨cell, after, cost, hsource, hrun, htrace, hsafe, hclosed, hstack, hs, hg, hv, ht, ho, hex, hlen,
    he, hn, hframe, fun _ _ hl => hl.stable hex⟩

theorem insert_loan_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ cell after cost,
      sourceRun MemoSource.Certificate.original.body fuel .insert
          [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      MemoSource.Heap.run Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost) ∧
      RunSafe memory Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Safe memory after cell (.adt .table) ∧ Unborrowed after cell ∧
      Stack.RunSafe Stack.Certificate.original Stack.Certificate.originalCount fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      (∀ frame, Spatial.Separated memory (tc :: frame) → Spatial.Separated after (cell :: frame)) ∧
      ∀ pointer ty, Loan memory pointer ty → ∃ target, read after pointer = some target ∧ Typed after target ty := by
  obtain ⟨cell, after, cost, hsource, hrun, hstack, hs, hg, hv, ht, hex, hlen, he, hn, htail, hframe⟩ :=
    Stack.insert_stack_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  obtain ⟨htrace, hsafe, hclosed, _⟩ := ordinary_loans fuel .insert (by decide) memory _
    (.cons (hTable.typed (table_typed table)) (.cons (hLeft.typed (.shared (word_typed left)))
      (.cons (hRight.typed (.shared (word_typed right))) (.cons (hResult.typed (.shared (result_typed result))) .nil)))) hrun
  exact ⟨cell, after, cost, hsource, hrun, htrace, hsafe, hclosed, hstack, hs, hg, hv, ht, hex, hlen,
    he, hn, htail, hframe, fun _ _ hl => hl.stable hex⟩

end SubtreeProofs.Rust.MemoSource.Borrow
