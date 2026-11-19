module

public import SubtreeProofs.Rust.SourceHeapResources

/-! Finite ghost readback constructs metadata from actual cells and pointer
targets, rather than running a source parent for its answer. The independent
budget bounds readback nesting, not production Rust work or call-nesting fuel. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  def valueDepth : Value → Nat
    | .boolean _ | .number _ => 1
    | .node _ _ fields => fieldsDepth fields + 1
    | .reference value | .boxed value => valueDepth value + 1

  def fieldsDepth : List Value → Nat
    | [] => 0
    | first :: rest => max (valueDepth first) (fieldsDepth rest)
end

theorem valueDepth_pos (value : Value) : 0 < valueDepth value := by
  cases value <;> simp only [valueDepth] <;> omega

def snapshotCollect (observe : Cell → Option (Value × List Nat)) : List Cell → Option (List Value × List Nat)
  | [] => some ([], [])
  | first :: rest => do
    let (value, reads) ← observe first
    let (values, more) ← snapshotCollect observe rest
    some (value :: values, reads ++ more)

def snapshot (fuel : Nat) (memory : Memory) (cell : Cell) : Option (Value × List Nat) :=
  match fuel with
  | 0 => none
  | fuel + 1 => match cell with
    | .boolean b => some (.boolean b, [])
    | .number n => some (.number n, [])
    | .node kind tag cells => do
      let (values, reads) ← snapshotCollect (snapshot fuel memory) cells
      some (.node kind tag values, reads)
    | .shared pointer => do
      let child ← read memory pointer
      let (value, reads) ← snapshot fuel memory child
      some (.reference value, reads ++ [pointer.root])
    | .owned address => do
      let child ← memory[address]?
      let (value, reads) ← snapshot fuel memory child
      some (.boxed value, reads ++ [address])
termination_by structural fuel

def snapshotFields (fuel : Nat) (memory : Memory) (cells : List Cell) : Option (List Value × List Nat) :=
  snapshotCollect (snapshot fuel memory) cells

theorem snapshot_node (fuel : Nat) (memory : Memory) (kind : Kind) (tag : Nat) (cells : List Cell) :
    snapshot (fuel + 1) memory (.node kind tag cells) = (do
      let (values, reads) ← snapshotFields fuel memory cells
      some (.node kind tag values, reads)) := rfl

theorem snapshotFields_nil (fuel : Nat) (memory : Memory) : snapshotFields fuel memory [] = some ([], []) := rfl

theorem snapshotFields_cons (fuel : Nat) (memory : Memory) (cell : Cell) (cells : List Cell) :
    snapshotFields fuel memory (cell :: cells) = (do
      let (value, reads) ← snapshot fuel memory cell
      let (values, more) ← snapshotFields fuel memory cells
      some (value :: values, reads ++ more)) := rfl

mutual
  theorem snapshot_spec (fuel : Nat) {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
      (h : snapshot fuel memory cell = some (value, reads)) : Graph memory cell value reads := by
    cases fuel with
    | zero => simp only [snapshot] at h; cases h
    | succ fuel =>
      cases cell with
      | boolean b => simp only [snapshot] at h; cases h; exact .boolean b
      | number n => simp only [snapshot] at h; cases h; exact .number n
      | node kind tag cells =>
        cases hs : snapshotFields fuel memory cells with
        | none => simp [snapshot_node, hs] at h
        | some pair =>
          rcases pair with ⟨values, used⟩
          simp only [snapshot_node, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .node (snapshotFields_spec fuel hs)
      | shared pointer =>
        cases hr : read memory pointer with
        | none => simp [snapshot, hr] at h
        | some child =>
          cases hs : snapshot fuel memory child with
          | none => simp [snapshot, hr, hs] at h
          | some pair =>
            rcases pair with ⟨value, used⟩
            simp only [snapshot, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .shared hr (snapshot_spec fuel hs)
      | owned address =>
        cases hr : memory[address]? with
        | none => simp [snapshot, hr] at h
        | some child =>
          cases hs : snapshot fuel memory child with
          | none => simp [snapshot, hr, hs] at h
          | some pair =>
            rcases pair with ⟨value, used⟩
            simp only [snapshot, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact .owned hr (snapshot_spec fuel hs)
  termination_by (fuel, sizeOf cell)

  theorem snapshotFields_spec (fuel : Nat) {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
      (h : snapshotFields fuel memory cells = some (values, reads)) : GraphFields memory cells values reads := by
    cases cells with
    | nil => simp only [snapshotFields_nil] at h; cases h; exact .nil
    | cons first rest =>
      cases hf : snapshot fuel memory first with
      | none => simp [snapshotFields_cons, hf] at h
      | some pair =>
        rcases pair with ⟨value, used⟩
        cases hr : snapshotFields fuel memory rest with
        | none => simp [snapshotFields_cons, hf, hr] at h
        | some pair =>
          rcases pair with ⟨values, more⟩
          simp only [snapshotFields_cons, hf, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact .cons (snapshot_spec fuel hf) (snapshotFields_spec fuel hr)
  termination_by (fuel, sizeOf cells)
end

mutual
  theorem Graph.snapshot {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
      (h : Graph memory cell value reads) (fuel : Nat) (bound : valueDepth value ≤ fuel) :
      snapshot fuel memory cell = some (value, reads) := by
    cases fuel with
    | zero => have hp := valueDepth_pos value; omega
    | succ fuel =>
      cases h with
      | boolean b | number b => simp only [snapshot]
      | @node kind tag cells values reads fields =>
        have hb : fieldsDepth values ≤ fuel := by simpa only [valueDepth, Nat.add_le_add_iff_right] using bound
        simp only [snapshot_node, fields.snapshot fuel hb, Bind.bind, Option.bind]
      | @shared pointer cell value reads hr child =>
        have hb : valueDepth value ≤ fuel := by simpa only [valueDepth, Nat.add_le_add_iff_right] using bound
        simp only [snapshot, hr, child.snapshot fuel hb, Bind.bind, Option.bind]
      | @owned address cell value reads hr child =>
        have hb : valueDepth value ≤ fuel := by simpa only [valueDepth, Nat.add_le_add_iff_right] using bound
        simp only [snapshot, hr, child.snapshot fuel hb, Bind.bind, Option.bind]

  theorem GraphFields.snapshot {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
      (h : GraphFields memory cells values reads) (fuel : Nat) (bound : fieldsDepth values ≤ fuel) :
      snapshotFields fuel memory cells = some (values, reads) := by
    cases h with
    | nil => simp only [snapshotFields_nil]
    | cons first rest =>
      have hb := Nat.max_le.mp bound
      simp only [snapshotFields_cons, first.snapshot fuel hb.1, rest.snapshot fuel hb.2, Bind.bind, Option.bind]
end

theorem represents_unique {memory : Memory} {cell : Cell} {first second : Value}
    (hfirst : Represents memory cell first) (hsecond : Represents memory cell second) : first = second := by
  obtain ⟨left, hl⟩ := graph_of_represents hfirst
  obtain ⟨right, hr⟩ := graph_of_represents hsecond
  have he := Option.some.inj ((hl.snapshot (max (valueDepth first) (valueDepth second)) (Nat.le_max_left ..)).symm.trans
    (hr.snapshot _ (Nat.le_max_right ..)))
  exact congrArg Prod.fst he

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
