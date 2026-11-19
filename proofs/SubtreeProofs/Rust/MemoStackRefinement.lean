module

public import SubtreeProofs.Rust.MemoStackCertificate
public import SubtreeProofs.Rust.MemoSpatialRefinement

/-! Retained source storage and initialization traces composed with actual
source/heap runs, ownership guards, separation and complete native costs. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Stack

open LookupSource LookupSource.Heap LookupSource.Heap.Spatial verified_ordered_core

theorem source_run_stack (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hrep : RepresentsFields memory cells values) (hargs : cells.length = arity function)
    (hr : sourceRun MemoSource.Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSafe Certificate.original Certificate.originalCount fuel function cells memory cell after cost ∧
      Represents after cell value ∧ Extends memory after ∧ after.length = memory.length + cost.events.allocations := by
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hrep hr
  exact ⟨cell, after, hrun, Certificate.original_run_safe fuel function cells memory hargs hrun, hv, hext, hlen⟩

theorem concatenate_stack_total (left right : BalancedWord) (fuel : Nat) (hf : concatenateDepth left right ≤ fuel)
    (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      sourceRun MemoSource.Certificate.original.body fuel .concatenate [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      MemoSource.Heap.run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSafe Certificate.original Certificate.originalCount fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      ∀ frame, Separated memory frame → Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hsource, hrun, hs, hg, hv, ht, ho, hext, hlen, he, hn, hframe⟩ :=
    Spatial.concatenate_spatial_total left right fuel hf memory pl pr hLeft hRight
  exact ⟨cell, after, cost, hsource, hrun, Certificate.original_run_safe fuel .concatenate _ memory rfl hrun,
    hs, hg, hv, ht, ho, hext, hlen, he, hn, hframe⟩

theorem insert_stack_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
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
      RunSafe Certificate.original Certificate.originalCount fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Spatial.RunSpatial Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      ∀ frame, Separated memory (tc :: frame) → Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hsource, hrun, hs, hg, hv, ht, hext, hlen, he, hn, htail, hframe⟩ :=
    Spatial.insert_spatial_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  exact ⟨cell, after, cost, hsource, hrun, Certificate.original_run_safe fuel .insert _ memory rfl hrun,
    hs, hg, hv, ht, hext, hlen, he, hn, htail, hframe⟩

end SubtreeProofs.Rust.MemoSource.Stack
