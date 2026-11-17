import SubtreeProofs.Rust.LookupSpatialRefinement

namespace LookupSpatialTests

open SubtreeProofs.Rust.LookupSource Heap Spatial

private def memory : Memory := [.node .word 0 [], .node .word 0 []]

private theorem fpZero : Footprint memory (.owned 0) [0] := .owned rfl (.node .nil)
private theorem fpOne : Footprint memory (.owned 1) [1] := .owned rfl (.node .nil)

-- Both owners are individually well typed; their joint footprint duplicates 0.
example : Typed memory (.owned 0) (.owned (.adt .word)) := .owned rfl (.node .emptyWord .nil)
example : ¬ Separated memory [.owned 0, .owned 0] := by
  rintro ⟨addresses, hf, hn⟩
  have hc : FieldsFootprint memory [.owned 0, .owned 0] [0, 0] := .cons fpZero (.cons fpZero .nil)
  have he := hf.unique hc
  subst addresses
  simp at hn

example : ¬ Separated memory [.node .word 1 [.owned 0, .owned 0]] := by
  rintro ⟨addresses, hf, hn⟩
  have hc : FieldsFootprint memory [.node .word 1 [.owned 0, .owned 0]] [0, 0] :=
    .cons (.node (.cons fpZero (.cons fpZero .nil))) .nil
  have he := hf.unique hc
  subst addresses
  simp at hn

example : Separated memory [.owned 0, .owned 1] :=
  ⟨[0, 1], .cons fpZero (.cons fpOne .nil), by decide⟩

-- Moving one owner preserves separation from another retained owner.
private def env : Locals := fun index => if index = 0 then some (.owned 0) else none
private theorem bounded : Bounded 1 env := by
  intro index hi
  simp [env, show index ≠ 0 by omega]

example : Separated memory ([.owned 0] ++ values 1 (env.set 0 none) ++ [.owned 1]) := by
  have hp := (operand_spatial (memory := memory) bounded (.move 0) rfl).2 [.owned 1]
  apply hp
  exact ⟨[0, 1], .cons fpZero (.cons fpOne .nil), by decide⟩

-- A new Box is separated from an old caller-owned Box, even with live payload.
example : Separated (memory ++ [.boolean true]) [.owned 2, .owned 0] := by
  have h : Separated memory [.boolean true, .owned 0] :=
    ⟨[0], .cons (.boolean true) (.cons fpZero .nil), by decide⟩
  exact h.alloc

-- Shared aliases add no owned occurrences, including references into a frame.
example : Separated memory [.shared ⟨0, []⟩, .shared ⟨0, []⟩, .owned 0] :=
  ⟨[0], .cons (.shared _) (.cons (.shared _) (.cons fpZero .nil)), by decide⟩

-- Actual lookup keeps every valid external owner frame separated.
example {cell : Cell} {after : Memory} {cost : Cost}
    (hr : Heap.run Program.body 3 .lookup
      [.shared ⟨0, []⟩, .shared ⟨1, []⟩, .shared ⟨1, []⟩]
      [.node .table 0 [], .node .word 0 []] = some (cell, after, cost))
    (frame : List Cell) (hs : Separated [.node .table 0 [], .node .word 0 []] frame) :
    Separated after (cell :: frame) :=
  ((lookup_spatial 3 _ _ _ _ hr).2 frame hs).1

end LookupSpatialTests
