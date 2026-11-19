module

public import SubtreeProofs.Rust.SourceEvalHeapMemo

/-! Native lookup-family inputs instantiate the existing source and exclusive
heap contracts in the mixed world. Concrete output readback is complete at its
finite depth bound; input shared aliases remain permitted. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage verified_ordered_core

theorem lookup_complete (fuel budget : Nat) {world : World} (hw : world.WellFormed)
    (function : LookupSource.Function) (packets : List ValueCell) {value : Value} {cost : LookupSource.Cost} {ty : Ty}
    (hb : Legacy.FieldsBounded (packets.map Prod.snd))
    (hp : RepresentsFields world.memory (packets.map Prod.fst) (packets.map Prod.snd))
    (hs : LookupSource.run LookupSource.Program.body fuel function (packets.map Prod.snd) = some (value, cost))
    (ht : SnapshotTyped value ty) (closed : Borrow.Closed ty)
    (owns : ∀ cell memory, Heap.run LookupSource.Program.body fuel function (packets.map Prod.fst) world.memory = some (cell, memory, cost) →
      Owns memory cell world.memory.length memory.length)
    (bound : valueDepth value ≤ budget) :
    ∃ cell memory,
      lookup fuel budget world function packets = some (world.boxSuffix memory, (cell, value), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel (SourceEval.Helpers.lookupFunction function) (packets.map Prod.snd) =
        some (value, Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell value ∧
      Owns memory cell world.memory.length memory.length ∧ (world.boxSuffix memory).WellFormed ∧
      (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨cell, memory, hr, hv, he, _⟩ := Heap.run_spec LookupSource.Program.body Heap.program_borrows fuel function world.memory _ _ _ _ hp hs
  have ho := owns cell memory hr
  have hread := readable_fresh hv (Borrow.typed_unborrowed (hv.typed ht) closed) ho
  exact ⟨cell, memory, finish_run hr (readPacket_complete hread budget bound),
    SourceEval.Helpers.lookup_normalized fuel function _ hb hs,
    hread, ho, hw.boxSuffix he, world.boxSuffix_keeps hw he⟩

theorem copy_total (word : BalancedWord) (fuel budget : Nat) (hf : wordHeight word ≤ fuel)
    {world : World} (hw : world.WellFormed) (pointer : Pointer)
    (hp : Readable world.memory world.live (.shared pointer) (.reference (encodeWord word)))
    (bound : valueDepth (encodeWord word) ≤ budget) :
    ∃ cell memory cost,
      lookup fuel budget world .copyWord [(.shared pointer, .reference (encodeWord word))] =
        some (world.boxSuffix memory, (cell, encodeWord word), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .copyWord [.reference (encodeWord word)] =
        some (encodeWord word, Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell (encodeWord word) ∧
      Owns memory cell world.memory.length memory.length ∧ (world.boxSuffix memory).WellFormed ∧
      (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨_, hg, _⟩ := hp
  obtain ⟨cost, hs, _⟩ := LookupSource.copy_source word fuel hf
  obtain ⟨cell, memory, rest⟩ := lookup_complete fuel budget hw .copyWord [(.shared pointer, .reference (encodeWord word))]
    (.cons (.reference (SourceEval.Helpers.word_bounded word)) .nil) (.cons hg.represents .nil) hs (word_typed word) (.adt .word)
    (fun cell memory hr => Heap.copy_return_owns word fuel hf world.memory pointer hg.represents hr) bound
  exact ⟨cell, memory, cost, rest⟩

theorem copyResult_total (result : CommonEmbedding) (fuel budget : Nat) (hf : wordHeight result.word + 1 ≤ fuel)
    {world : World} (hw : world.WellFormed) (pointer : Pointer)
    (hp : Readable world.memory world.live (.shared pointer) (.reference (encodeResult result)))
    (bound : valueDepth (encodeResult result) ≤ budget) :
    ∃ cell memory cost,
      lookup fuel budget world .copyResult [(.shared pointer, .reference (encodeResult result))] =
        some (world.boxSuffix memory, (cell, encodeResult result), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .copyResult [.reference (encodeResult result)] =
        some (encodeResult result, Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell (encodeResult result) ∧
      Owns memory cell world.memory.length memory.length ∧ (world.boxSuffix memory).WellFormed ∧
      (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨_, hg, _⟩ := hp
  obtain ⟨cost, hs, _⟩ := LookupSource.copyResult_source result fuel hf
  obtain ⟨cell, memory, rest⟩ := lookup_complete fuel budget hw .copyResult [(.shared pointer, .reference (encodeResult result))]
    (.cons (.reference (SourceEval.Helpers.result_bounded result)) .nil) (.cons hg.represents .nil) hs (result_typed result) (.adt .embedding)
    (fun cell memory hr => Heap.copyResult_return_owns result fuel hf world.memory pointer hg.represents hr) bound
  exact ⟨cell, memory, cost, rest⟩

theorem lookup_total (table : MemoTable) (left right : BalancedWord) (fuel budget : Nat)
    (hf : lookupDepth table left right ≤ fuel) {world : World} (hw : world.WellFormed) (pt pl pr : Pointer)
    (ht : Readable world.memory world.live (.shared pt) (.reference (encodeTable table)))
    (hl : Readable world.memory world.live (.shared pl) (.reference (encodeWord left)))
    (hr : Readable world.memory world.live (.shared pr) (.reference (encodeWord right)))
    (bound : valueDepth (encodeOption (LookupEvents.lookup table left right).1) ≤ budget) :
    ∃ cell memory cost,
      lookup fuel budget world .lookup [(.shared pt, .reference (encodeTable table)),
        (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))] =
        some (world.boxSuffix memory, (cell, encodeOption (LookupEvents.lookup table left right).1), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .lookup
        [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeOption (LookupEvents.lookup table left right).1, Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell (encodeOption (LookupEvents.lookup table left right).1) ∧
      Owns memory cell world.memory.length memory.length ∧ (world.boxSuffix memory).WellFormed ∧
      (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨_, htgraph, _⟩ := ht
  obtain ⟨_, hlgraph, _⟩ := hl
  obtain ⟨_, hrgraph, _⟩ := hr
  obtain ⟨cost, hs, _⟩ := LookupSource.lookup_source table left right fuel hf
  obtain ⟨cell, memory, rest⟩ := lookup_complete fuel budget hw .lookup [(.shared pt, .reference (encodeTable table)),
    (.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
    (.cons (.reference (SourceEval.Helpers.table_bounded table)) (.cons (.reference (SourceEval.Helpers.word_bounded left))
      (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil)))
    (.cons htgraph.represents (.cons hlgraph.represents (.cons hrgraph.represents .nil))) hs
    (option_typed _) (.adt .optional)
    (fun cell memory hr => Heap.lookup_return_owns table left right fuel hf world.memory pt pl pr
      htgraph.represents hlgraph.represents hrgraph.represents hr) bound
  exact ⟨cell, memory, cost, rest⟩

theorem compare_total (left right : BalancedWord) (fuel budget : Nat) (hf : wordHeight left ≤ fuel)
    {world : World} (hw : world.WellFormed) (pl pr : Pointer)
    (hl : Readable world.memory world.live (.shared pl) (.reference (encodeWord left)))
    (hr : Readable world.memory world.live (.shared pr) (.reference (encodeWord right))) (bound : 1 ≤ budget) :
    ∃ memory cost,
      lookup fuel budget world .compare [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))] =
        some (world.boxSuffix memory, (.boolean (LookupEvents.compare left right).1, .boolean (LookupEvents.compare left right).1), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .compare [.reference (encodeWord left), .reference (encodeWord right)] =
        some (.boolean (LookupEvents.compare left right).1, Legacy.costMap cost) ∧
      (world.boxSuffix memory).WellFormed ∧ (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨_, hlgraph, _⟩ := hl
  obtain ⟨_, hrgraph, _⟩ := hr
  obtain ⟨cost, hs, _⟩ := LookupSource.compare_source left right fuel hf
  obtain ⟨cell, memory, hrun, hsource, hread, _, hworld, hkeep⟩ := lookup_complete fuel budget hw .compare
    [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))]
    (.cons (.reference (SourceEval.Helpers.word_bounded left)) (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil))
    (.cons hlgraph.represents (.cons hrgraph.represents .nil)) hs (.boolean _) .boolean (by
      intro cell memory hc
      obtain ⟨cost', he, _⟩ := Heap.compare_spec left right world.memory _
        (.cons hlgraph.represents (.cons hrgraph.represents .nil)) fuel hf
      have hh := Option.some.inj (hc.symm.trans he)
      simp only [Prod.mk.injEq] at hh
      obtain ⟨rfl, rfl, _⟩ := hh
      exact .boolean _ _) bound
  obtain ⟨_, hg, _⟩ := hread
  cases hg
  exact ⟨memory, cost, hrun, hsource, hworld, hkeep⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
