module

public import SubtreeProofs.Rust.SourceCallRetainedContext

/-! Native immutable referents cannot read an uninitialized empty-tuple cell or
a cell containing another shared pointer. This is a structural graph fact,
preserving repeated aliases. It supplies initialization permissions for the
actual evaluator's fresh destinations and moves of reference-valued locals. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

def InvalidLoanCell (cell : Cell) : Prop :=
  cell = .node .tuple 0 [] ∨ ∃ pointer, cell = .shared pointer

mutual
  inductive NativeData : Value → Prop where
    | boolean (value : Bool) : NativeData (.boolean value)
    | number (value : Nat) : NativeData (.number value)
    | node {kind : Kind} {tag : Nat} {values : List Value} :
        (kind = .tuple → tag = 0 → values ≠ []) → NativeDataFields values → NativeData (.node kind tag values)
    | owned {value : Value} : NativeData value → NativeData (.boxed value)

  inductive NativeDataFields : List Value → Prop where
    | nil : NativeDataFields []
    | cons {value : Value} {values : List Value} : NativeData value → NativeDataFields values → NativeDataFields (value :: values)
end

theorem Graph.native_cell {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
    (h : Graph memory cell value reads) (data : NativeData value) : ¬ InvalidLoanCell cell := by
  cases data with
  | boolean _ | number _ | owned _ => cases h; simp [InvalidLoanCell]
  | node nonempty _ => cases h with
    | node fields =>
      intro bad
      rcases bad with tuple | ⟨pointer, pointerEq⟩
      · cases tuple
        cases fields
        exact nonempty rfl rfl rfl
      · cases pointerEq

theorem fields_invalid_cell {cell result : Cell} (bad : InvalidLoanCell cell) {path : List Nat}
    (read : Heap.fields cell path = some result) : result = cell := by
  cases path with
  | nil => cases read; rfl
  | cons _ _ =>
    rcases bad with rfl | ⟨pointer, rfl⟩ <;> simp only [Heap.fields, List.getElem?_nil, bind, Option.bind, reduceCtorEq] at read

theorem read_native_root {memory : Memory} {pointer : Pointer} {cell : Cell} {value : Value} {reads : List Nat}
    (read : Heap.read memory pointer = some cell) (graph : Graph memory cell value reads) (data : NativeData value)
    {raw : Cell} (root : memory[pointer.root]? = some raw) : ¬ InvalidLoanCell raw := by
  intro bad
  have selected : Heap.fields raw pointer.path = some cell := by
    simpa only [Heap.read, root, bind, Option.bind] using read
  have same := fields_invalid_cell bad selected
  exact graph.native_cell data (same ▸ bad)

mutual
  theorem Graph.native_reads {memory : Memory} {cell : Cell} {value : Value} {reads : List Nat}
      (h : Graph memory cell value reads) (data : NativeData value) :
      ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ InvalidLoanCell raw := by
    cases data with
    | boolean _ | number _ => cases h; simp
    | node _ fields => cases h with
      | node graphs => exact graphs.native_reads fields
    | owned child => cases h with
      | @owned address cell value reads lookup graph =>
        intro target member raw root
        rcases List.mem_append.mp member with old | fresh
        · exact graph.native_reads child target old raw root
        · have same : target = address := List.mem_singleton.mp fresh
          subst target
          have eq := Option.some.inj (lookup.symm.trans root)
          subst raw
          exact graph.native_cell child
  termination_by sizeOf value

  theorem GraphFields.native_reads {memory : Memory} {cells : List Cell} {values : List Value} {reads : List Nat}
      (h : GraphFields memory cells values reads) (data : NativeDataFields values) :
      ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ InvalidLoanCell raw := by
    cases data with
    | nil => cases h; simp
    | cons first rest => cases h with
      | cons graph graphs =>
        intro address member raw lookup
        rcases List.mem_append.mp member with head | tail
        · exact graph.native_reads first address head raw lookup
        · exact graphs.native_reads rest address tail raw lookup
  termination_by sizeOf values
end

theorem Graph.shared_native_reads {memory : Memory} {pointer : Pointer} {value : Value} {reads : List Nat}
    (h : Graph memory (.shared pointer) (.reference value) reads) (data : NativeData value) :
    ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ InvalidLoanCell raw := by
  cases h with
  | shared read graph =>
    intro address member raw lookup
    rcases List.mem_append.mp member with child | root
    · exact graph.native_reads data address child raw lookup
    · have same : address = pointer.root := List.mem_singleton.mp root
      subst address
      exact read_native_root read graph data lookup

mutual
  inductive LoanSafe : Slot → Prop where
    | empty : LoanSafe .empty
    | boolean (value : Bool) : LoanSafe (.boolean value)
    | number (value : Nat) : LoanSafe (.number value)
    | node {kind : Kind} {tag : Nat} {parts : List Slot} : LoanSafeFields parts → LoanSafe (.node kind tag parts)
    | shared {value : Value} : NativeData value → LoanSafe (.shared value)
    | owned {part : Slot} : LoanSafe part → LoanSafe (.boxed part)

  inductive LoanSafeFields : List Slot → Prop where
    | nil : LoanSafeFields []
    | cons {part : Slot} {parts : List Slot} : LoanSafe part → LoanSafeFields parts → LoanSafeFields (part :: parts)
end

mutual
  theorem LoanSafe.of_closed {part : Slot} {ty : Ty} (typed : SlotTyped part ty) (closed : Borrow.Closed ty) : LoanSafe part := by
    cases typed with
    | empty _ => exact .empty
    | boolean value => exact .boolean value
    | number _ => exact .number _
    | shared _ => cases closed
    | owned typed => cases closed with
      | owned inner => exact .owned (LoanSafe.of_closed typed inner)
    | node shape fields => exact .node (LoanSafeFields.of_closed fields (Borrow.shape_closed shape closed))
  termination_by sizeOf part

  theorem LoanSafeFields.of_closed {parts : List Slot} {types : List Ty}
      (typed : FieldsSlotTyped parts types) (closed : Borrow.ClosedFields types) : LoanSafeFields parts := by
    cases typed with
    | nil => exact .nil
    | cons first rest => cases closed with
      | cons head tail => exact .cons (LoanSafe.of_closed first head) (LoanSafeFields.of_closed rest tail)
  termination_by sizeOf parts
end

mutual
  theorem BorrowFootprint.safe_cells {memory : Memory} {cell : Cell} {part : Slot} {loans : List Nat}
      (h : BorrowFootprint memory cell part loans) (safe : LoanSafe part) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ InvalidLoanCell raw := by
    cases h with
    | empty _ | boolean _ | number _ => simp
    | shared graph => cases safe with
      | shared data => exact graph.shared_native_reads data
    | node fields => cases safe with
      | node parts => exact fields.safe_cells parts
    | owned _ child => cases safe with
      | owned inner => exact child.safe_cells inner
  termination_by sizeOf part

  theorem BorrowFields.safe_cells {memory : Memory} {cells : List Cell} {parts : List Slot} {loans : List Nat}
      (h : BorrowFields memory cells parts loans) (safe : LoanSafeFields parts) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ InvalidLoanCell raw := by
    cases h with
    | nil => simp
    | cons first rest => cases safe with
      | cons head tail =>
        intro address member raw lookup
        rcases List.mem_append.mp member with left | right
        · exact first.safe_cells head address left raw lookup
        · exact rest.safe_cells tail address right raw lookup
  termination_by sizeOf parts
end

namespace Storage

theorem LocalResources.safe_cells {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) (safe : LoanSafe (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ InvalidLoanCell raw := by
  cases h with
  | vacant _ _ => simp
  | stored _ _ _ represented _ => exact represented.borrowed.safe_cells safe

theorem Inventory.safe_cells {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r)
    (safe : ∀ slot ∈ slots, LoanSafe (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ InvalidLoanCell raw := by
  induction h with
  | nil => simp
  | @cons slot slots head tail first rest ih =>
    intro address member raw lookup
    rcases List.mem_append.mp member with left | right
    · exact first.safe_cells (safe slot (by simp)) address left raw lookup
    · exact ih (fun slot member => safe slot (List.mem_cons_of_mem _ member)) address right raw lookup

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
