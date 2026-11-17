import SubtreeProofs.Rust.MemoRegionRefinement

namespace MemoRegionTests

open SubtreeProofs.Rust LookupSource LookupSource.Heap verified_ordered_core

-- The owned table contributes a value argument, not another shared lifetime.
example : MemoSource.arity .insert = 4 := rfl
example : MemoSource.Regions.regionArity .insert = 3 := rfl

private def memory : Memory := [.node .word 0 []]
private def tagged : Regions.Ty := .shared (.body 0) (.adt .word)
private theorem safe : Borrow.Safe memory memory (.shared ⟨0, []⟩) (.shared (.adt .word)) :=
  .shared ⟨⟨_, rfl, .node .emptyWord .nil⟩⟩

example : Regions.ScopedValue memory memory (.body 1) (Regions.callLifetime memory) (.shared ⟨0, []⟩) tagged := by
  apply (Regions.scoped_erasure_iff (.refl memory) (Regions.Scoped.shared (by change 0 < 1; decide) (.adt .word)) _).mpr
  simpa only [tagged, Regions.erase] using safe

-- A typed old read needs the lifetime valuation as well as source scope.
example : ¬Regions.Value memory memory (fun _ _ => False) (.shared ⟨0, []⟩) tagged := by
  intro h
  cases h with | shared _ _ hlive _ => cases hlive
example : ¬Regions.Scoped (.body 1) (.shared (.body 9) (.adt .word)) := by
  intro h
  cases h with | shared hb _ => change 9 < 1 at hb; omega

example : ∃ program, MemoSource.Regions.read MemoSource.Input.Program.source = .ok program ∧ ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 2 .concatenate [.shared ⟨0, []⟩, .shared ⟨0, []⟩] memory =
      some (cell, after, cost) ∧
    MemoSource.Regions.RunScoped memory program MemoSource.Program.body 2 .concatenate
      [.shared ⟨0, []⟩, .shared ⟨0, []⟩] memory cell after cost ∧ Borrow.Unborrowed after cell := by
  obtain ⟨program, hread, cell, after, cost, _, hr, hscoped, _, _, hclosed, _⟩ :=
    MemoSource.Regions.concatenate_source_total .Empty .Empty 2 (by decide +kernel) memory ⟨0, []⟩ ⟨0, []⟩
      (.shared rfl (.node .nil)) (.shared rfl (.node .nil))
  exact ⟨program, hread, cell, after, cost, hr, hscoped, hclosed⟩

private def word : Cell := .node .word 0 []
private def witness : CommonEmbedding := ⟨.Empty, 77#u32⟩
private def entry : Cell := .node .entry 0 [word, word, .node .embedding 0 [word, .number 77]]
private def tableMemory : Memory := [entry, .node .table 0 []]
private def table : Cell := .node .table 1 [.owned 0, .owned 1]
private def native : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty
private theorem table_rep : Represents tableMemory table (encodeTable native) :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))
private theorem key_rep : Represents tableMemory (.shared ⟨0, [0]⟩) (.reference (encodeWord .Empty)) := .shared rfl (.node .nil)
private theorem result_rep : Represents tableMemory (.shared ⟨0, [2]⟩) (.reference (encodeResult witness)) :=
  .shared rfl (.node (.cons (.node .nil) (.cons (.number 77) .nil)))

-- Every recursive scoped call retains source annotations even while queries
-- and the witness borrow into the owned table transferred to the new tail.
example : ∃ program, MemoSource.Regions.read MemoSource.Input.Program.source = .ok program ∧ ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] tableMemory = some (cell, after, cost) ∧
    MemoSource.Regions.RunScoped tableMemory program MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] tableMemory cell after cost ∧
    Borrow.Unborrowed after cell := by
  obtain ⟨program, hread, cell, after, cost, _, hr, hscoped, _, _, hclosed, _⟩ :=
    MemoSource.Regions.insert_source_total native .Empty .Empty witness 4 (by decide +kernel)
      tableMemory table ⟨0, [0]⟩ ⟨0, [0]⟩ ⟨0, [2]⟩ table_rep key_rep key_rep result_rep
  exact ⟨program, hread, cell, after, cost, hr, hscoped, hclosed⟩

end MemoRegionTests
