module

public import SubtreeProofs.Rust.MemoSpatialCalls
public import SubtreeProofs.Rust.MemoFrameRefinement

/-! Actual source/heap executions composed with recursive local guards and
spatial traces, including insertion's owned argument and suspended callers. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Spatial

open LookupSource LookupSource.Heap LookupSource.Heap.Spatial verified_ordered_core

theorem concatenate_spatial (fuel : Nat) (memory : Memory) (pl pr : Pointer)
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost)) :
    RunSpatial Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      ∀ frame, Separated memory frame → Separated after (cell :: frame) ∧ Extends memory after := by
  obtain ⟨hg, hp⟩ := original_spatial fuel .concatenate _ memory cell after cost (Frame.concatenate_profile pl pr) hr
  refine ⟨hg, Frame.concatenate_guarded fuel memory pl pr hr, ?_⟩
  intro frame hs
  exact hp frame ((Separated.plain_fields (.cons (.shared pl) (.cons (.shared pr) .nil))).mpr hs)

theorem insert_spatial (fuel : Nat) (memory : Memory) (table : Cell) (pl pr pc : Pointer)
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : MemoSource.Heap.run Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost)) :
    RunSpatial Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      ∀ frame, Separated memory (table :: frame) → Separated after (cell :: frame) ∧ Extends memory after := by
  obtain ⟨hg, hp⟩ := original_spatial fuel .insert _ memory cell after cost (Frame.insert_profile table pl pr pc) hr
  refine ⟨hg, Frame.insert_guarded fuel memory table pl pr pc hr, ?_⟩
  intro frame hs
  have hs' : Separated memory ([Cell.shared pl, .shared pr, .shared pc] ++ (table :: frame)) :=
    (Separated.plain_fields (.cons (.shared pl) (.cons (.shared pr) (.cons (.shared pc) .nil)))).mpr hs
  exact hp frame (hs'.perm (List.perm_middle (a := table) (l₁ := [Cell.shared pl, .shared pr, .shared pc]) (l₂ := frame)))

theorem source_run_spatial (fuel : Nat) (function : Function) (memory : Memory)
    (cells : List Cell) (values : List Value) (value : Value) (cost : Cost)
    (hrep : RepresentsFields memory cells values) (hargs : Frame.ArgsMatch function cells)
    (hr : sourceRun Certificate.original.body fuel function values = some (value, cost)) :
    ∃ cell after, MemoSource.Heap.run Program.body fuel function cells memory = some (cell, after, cost) ∧
      RunSpatial Program.body fuel function cells memory cell after cost ∧
      Frame.RunSafe Program.body fuel function cells memory cell after cost ∧
      Represents after cell value ∧ Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      ∀ frame, Separated memory (cells ++ frame) → Separated after (cell :: frame) := by
  obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := MemoSource.Heap.certified_run_spec fuel function memory cells values value cost hrep hr
  obtain ⟨hs, hp⟩ := original_spatial fuel function cells memory cell after cost hargs hrun
  exact ⟨cell, after, hrun, hs, Frame.original_run_safe fuel function cells memory hargs hrun, hv, hext, hlen,
    fun frame hf => (hp frame hf).1⟩

theorem concatenate_spatial_total (left right : BalancedWord) (fuel : Nat) (hf : concatenateDepth left right ≤ fuel)
    (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cell after cost,
      sourceRun Certificate.original.body fuel .concatenate [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      MemoSource.Heap.run Program.body fuel .concatenate [.shared pl, .shared pr] memory = some (cell, after, cost) ∧
      RunSpatial Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .concatenate [.shared pl, .shared pr] memory cell after cost ∧
      Represents after cell (encodeWord (OrderedSolver.appendWord left right)) ∧ Typed after cell (.adt .word) ∧
      Owns after cell memory.length after.length ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations ∧ cost.events = concatenateEvents left right ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      ∀ frame, Separated memory frame → Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hsource, hrun, hv, ht, ho, hext, hlen, he, hn, hframe⟩ :=
    MemoSource.Heap.concatenate_total left right fuel hf memory pl pr hLeft hRight
  obtain ⟨hs, hg, _⟩ := concatenate_spatial fuel memory pl pr hrun
  exact ⟨cell, after, cost, hsource, hrun, hs, hg, hv, ht, ho, hext, hlen, he, hn, hframe⟩

theorem insert_spatial_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (tc : Cell) (pl pr pc : Pointer)
    (hTable : Represents memory tc (encodeTable table))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ cell after cost,
      sourceRun Certificate.original.body fuel .insert
          [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      MemoSource.Heap.run Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory = some (cell, after, cost) ∧
      RunSpatial Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Frame.RunSafe Program.body fuel .insert [tc, .shared pl, .shared pr, .shared pc] memory cell after cost ∧
      Represents after cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Typed after cell (.adt .table) ∧
      Extends memory after ∧ after.length = memory.length + cost.events.allocations ∧
      cost.events = insertEvents left right result ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ after[tail]? = some tc ∧ memory.length ≤ tail) ∧
      ∀ frame, Separated memory (tc :: frame) → Separated after (cell :: frame) := by
  obtain ⟨cell, after, cost, hsource, hrun, hv, ht, hext, hlen, he, hn, htail, hframe⟩ :=
    MemoSource.Heap.insert_total table left right result fuel hf memory tc pl pr pc hTable hLeft hRight hResult
  obtain ⟨hs, hg, _⟩ := insert_spatial fuel memory tc pl pr pc hrun
  exact ⟨cell, after, cost, hsource, hrun, hs, hg, hv, ht, hext, hlen, he, hn, htail, hframe⟩

end SubtreeProofs.Rust.MemoSource.Spatial
