module

public import SubtreeProofs.Rust.SourceHeapOutputReadback

/-! Complete actual concatenate/insertion helper execution over a mixed prefix.
Native inputs and independent read/owner contracts discharge source calls,
output readback and liveness; no desired helper result is a hypothesis. Existing
insertion owner ledgers and its transferred table tail remain explicit. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage verified_ordered_core

theorem concatenate_total (left right : BalancedWord) (fuel budget : Nat)
    (hf : MemoSource.concatenateDepth left right ≤ fuel) {world : World} (hw : world.WellFormed)
    (pl pr : Pointer)
    (hl : Readable world.memory world.live (.shared pl) (.reference (encodeWord left)))
    (hr : Readable world.memory world.live (.shared pr) (.reference (encodeWord right)))
    (bound : valueDepth (encodeWord (OrderedSolver.appendWord left right)) ≤ budget) :
    ∃ cell memory cost,
      memo fuel budget world .concatenate [(.shared pl, .reference (encodeWord left)), (.shared pr, .reference (encodeWord right))] =
        some (world.boxSuffix memory, (cell, encodeWord (OrderedSolver.appendWord left right)), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .concatenate
        [.reference (encodeWord left), .reference (encodeWord right)] =
        some (encodeWord (OrderedSolver.appendWord left right), Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell (encodeWord (OrderedSolver.appendWord left right)) ∧
      Owns memory cell world.memory.length memory.length ∧ (world.boxSuffix memory).WellFormed ∧
      (∀ guards, Keeps world (world.boxSuffix memory) guards) ∧ cost.events = MemoSource.concatenateEvents left right := by
  obtain ⟨_, hlrep, _⟩ := hl
  obtain ⟨_, hrrep, _⟩ := hr
  obtain ⟨cell, memory, cost, hs, he, hv, ht, ho, hext, _, events, _, _⟩ :=
    MemoSource.Heap.concatenate_total left right fuel hf world.memory pl pr hlrep.represents hrrep.represents
  have hread := readable_fresh hv (Borrow.typed_unborrowed ht (.adt .word)) ho
  have hp := readPacket_complete hread budget bound
  refine ⟨cell, memory, cost, ?_, ?_, hread, ho, hw.boxSuffix hext, world.boxSuffix_keeps hw hext, events⟩
  · exact finish_run (by simpa only [List.map_cons, List.map_nil] using he) hp
  · exact (SourceEval.Helpers.memo_run fuel .concatenate _ _ cost
      (.cons (.reference (SourceEval.Helpers.word_bounded left))
        (.cons (.reference (SourceEval.Helpers.word_bounded right)) .nil)) hs).2

theorem insert_total (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel budget : Nat)
    (hf : MemoSource.insertDepth left right result ≤ fuel) {world : World} (hw : world.WellFormed)
    (tc : Cell) (pl pr pc : Pointer)
    (ht : Readable world.memory world.live tc (encodeTable table))
    (hl : Readable world.memory world.live (.shared pl) (.reference (encodeWord left)))
    (hr : Readable world.memory world.live (.shared pr) (.reference (encodeWord right)))
    (hc : Readable world.memory world.live (.shared pc) (.reference (encodeResult result)))
    (bound : valueDepth (encodeTable (.Entry ⟨left, right, result⟩ table)) ≤ budget) :
    ∃ cell memory cost old owners,
      memo fuel budget world .insert [(tc, encodeTable table), (.shared pl, .reference (encodeWord left)),
        (.shared pr, .reference (encodeWord right)), (.shared pc, .reference (encodeResult result))] =
        some (world.boxSuffix memory, (cell, encodeTable (.Entry ⟨left, right, result⟩ table)), Legacy.costMap cost) ∧
      SourceEval.run SourceEval.Certificate.original.body fuel .insert
        [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
        some (encodeTable (.Entry ⟨left, right, result⟩ table), Legacy.costMap cost) ∧
      Readable (world.boxSuffix memory).memory (world.boxSuffix memory).live cell (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧
      Footprint world.memory tc old ∧ Footprint memory cell owners ∧
      owners.Perm (old ++ List.range' world.memory.length (memory.length - world.memory.length)) ∧
      owners.length = old.length + cost.events.allocations ∧ (old.Nodup → owners.Nodup) ∧
      AliveOn (world.boxSuffix memory).live owners ∧
      (∃ entry tail, cell = .node .table 1 [entry, .owned tail] ∧ memory[tail]? = some tc ∧ world.memory.length ≤ tail) ∧
      (world.boxSuffix memory).WellFormed ∧ (∀ guards, Keeps world (world.boxSuffix memory) guards) := by
  obtain ⟨old, howners, halive⟩ := readable_owners ht
  obtain ⟨_, htrep, _⟩ := ht
  obtain ⟨_, hlrep, _⟩ := hl
  obtain ⟨_, hrrep, _⟩ := hr
  obtain ⟨_, hcrep, _⟩ := hc
  obtain ⟨cell, memory, cost, hs, he, hv, htyped, hext, _, _, _, htail, _⟩ :=
    MemoSource.Heap.insert_total table left right result fuel hf world.memory tc pl pr pc
      htrep.represents hlrep.represents hrrep.represents hcrep.represents
  obtain ⟨owners, ho, hperm, hlen, hn⟩ :=
    MemoSource.Heap.insert_return_ledger table left right result fuel hf world.memory tc pl pr pc
      htrep.represents hlrep.represents hrrep.represents hcrep.represents he howners
  have hread := readable_transfer hw hext hv (Borrow.typed_unborrowed htyped (.adt .table)) ho halive hperm
  have hp := readPacket_complete hread budget bound
  refine ⟨cell, memory, cost, old, owners, ?_, ?_, hread, howners, ho, hperm, hlen, hn,
    World.boxSuffix_transfer_alive hw hext halive hperm, htail, hw.boxSuffix hext, world.boxSuffix_keeps hw hext⟩
  · exact finish_run (by simpa only [List.map_cons, List.map_nil] using he) hp
  · exact (SourceEval.Helpers.memo_run fuel .insert _ _ cost
      (.cons (SourceEval.Helpers.table_bounded table) (.cons (.reference (SourceEval.Helpers.word_bounded left))
        (.cons (.reference (SourceEval.Helpers.word_bounded right)) (.cons (.reference (SourceEval.Helpers.result_bounded result)) .nil)))) hs).2

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
