import SubtreeProofs.Rust.MemoSpatialRefinement

/-! Owner-profile and concrete trace regressions. Synthetic instruction
fragments are not compiled Rust mutants; actual bodies have kernel certificates. -/

namespace MemoSpatialTests

open SubtreeProofs.Rust LookupSource LookupSource.Heap verified_ordered_core

example : MemoSource.Frame.callProfile .insert [true, false, false, false] = true := rfl
-- A definitely plain value may be widened to the may-own table role.
example : MemoSource.Frame.callProfile .insert [false, false, false, false] = true := rfl
example : MemoSource.Frame.callProfile .insert [true, true, false, false] = false := rfl
example : MemoSource.Frame.callProfile .copyWord [true] = false := rfl
example : MemoSource.Frame.callProfile .boxNew [true] = true := rfl

private def initial := Frame.initialState 15 (MemoSource.Frame.inputFlags .insert)

-- A live owned input cannot be cleared, overwritten or conditionally dropped.
example : Frame.inferActionWith MemoSource.Frame.callProfile MemoSource.Frame.outputFlag initial (.scope 1) = none := by decide +kernel
example : Frame.inferActionWith MemoSource.Frame.callProfile MemoSource.Frame.outputFlag initial
    (.assign 1 (.use (.boolean true))) = none := by decide +kernel
example : Frame.inferActionWith MemoSource.Frame.callProfile MemoSource.Frame.outputFlag initial (.dropMoved 1) = none := by decide +kernel
example : Frame.inferOperands initial [.move 1, .move 1] = none := by decide +kernel
example : Frame.returnCheck [some true, some true] true = false := rfl

-- Once transferred out of the slot, clearing it is permitted.
example : Frame.inferActionWith MemoSource.Frame.callProfile MemoSource.Frame.outputFlag (initial.set 1 none) (.scope 1) =
    some ((initial.set 1 none).set 1 none) := by decide +kernel

-- Initial owner enumeration preserves the actual owned argument occurrence.
example : Spatial.values 8 (initialLocals [.owned 0, .shared ⟨0, []⟩]) = [.owned 0, .shared ⟨0, []⟩] := rfl
example (args : List Cell) : Spatial.values (args.length + 1) (initialLocals args) = args :=
  Spatial.values_initial args _ (by omega)

private def word : Cell := .node .word 0 []
private def witness : CommonEmbedding := ⟨.Empty, 77#u32⟩
private def entry : Cell := .node .entry 0 [word, word, .node .embedding 0 [word, .number 77]]
private def memory : Memory := [entry, .node .table 0 [], .number 12]
private def table : Cell := .node .table 1 [.owned 0, .owned 1]
private def native : MemoTable := .Entry ⟨.Empty, .Empty, witness⟩ .Empty

private theorem entry_footprint : Footprint memory entry [] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))
private theorem table_footprint : Footprint memory table [0, 1] :=
  .node (.cons (.owned rfl entry_footprint) (.cons (.owned rfl (.node .nil)) .nil))
private theorem frame_separated : Spatial.Separated memory [table, .owned 2] :=
  ⟨[0, 1, 2], .cons table_footprint (.cons (.owned rfl (.number 12)) .nil), by decide +kernel⟩

private theorem table_rep : Represents memory table (encodeTable native) :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 77) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))
private theorem key_rep : Represents memory (.shared ⟨0, [0]⟩) (.reference (encodeWord .Empty)) := .shared rfl (.node .nil)
private theorem result_rep : Represents memory (.shared ⟨0, [2]⟩) (.reference (encodeResult witness)) :=
  .shared rfl (.node (.cons (.node .nil) (.cons (.number 77) .nil)))

-- Both keys and the witness borrow into the owned table. Concrete recursive
-- guarded/spatial traces preserve an independent external owner throughout.
example : ∃ cell after cost,
    MemoSource.Heap.run MemoSource.Program.body 4 .insert
        [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory = some (cell, after, cost) ∧
    MemoSource.Spatial.RunSpatial MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory cell after cost ∧
    MemoSource.Frame.RunSafe MemoSource.Program.body 4 .insert
      [table, .shared ⟨0, [0]⟩, .shared ⟨0, [0]⟩, .shared ⟨0, [2]⟩] memory cell after cost ∧
    Spatial.Separated after [cell, .owned 2] := by
  obtain ⟨cell, after, cost, _, hr, hs, hg, _⟩ := MemoSource.Spatial.insert_spatial_total native .Empty .Empty witness
    4 (by decide +kernel) memory table ⟨0, [0]⟩ ⟨0, [0]⟩ ⟨0, [2]⟩ table_rep key_rep key_rep result_rep
  have hp := (MemoSource.Spatial.insert_spatial 4 memory table ⟨0, [0]⟩ ⟨0, [0]⟩ ⟨0, [2]⟩ hr).2.2
  exact ⟨cell, after, cost, hr, hs, hg, (hp [.owned 2] frame_separated).1⟩

-- A duplicated external owner fails the spatial premise, even though the
-- local owner-class guards alone do not identify individual Box addresses.
example : ¬Spatial.Separated memory [table, .owned 0] := by
  intro hs
  have hp : FieldsFootprint memory [table, .owned 0] [0, 1, 0] :=
    .cons table_footprint (.cons (.owned rfl entry_footprint) .nil)
  exact (by decide +kernel : ¬([0, 1, 0] : List Nat).Nodup) (hs.every_footprint hp)

end MemoSpatialTests
