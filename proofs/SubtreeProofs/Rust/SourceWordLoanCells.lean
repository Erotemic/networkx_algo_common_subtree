module

public import SubtreeProofs.Rust.SourceInlineMovePermissions

/-! Word referents cannot read a table root, a shared-pointer cell, or a tuple
whose inline fields all have that same exclusion. This follows from the actual
word graph and field projection rules and permits aliases with table-owned data. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap verified_ordered_core

inductive WordOpaque : Cell → Prop where
  | boolean (value : Bool) : WordOpaque (.boolean value)
  | number (value : Nat) : WordOpaque (.number value)
  | shared (pointer : Pointer) : WordOpaque (.shared pointer)
  | owned (address : Nat) : WordOpaque (.owned address)
  | node {kind : Kind} {tag : Nat} {cells : List Cell} (different : kind ≠ .word)
      (fields : ∀ cell ∈ cells, WordOpaque cell) : WordOpaque (.node kind tag cells)

theorem WordOpaque.fields {cell found : Cell} (opaqueCell : WordOpaque cell) {path : List Nat}
    (read : Heap.fields cell path = some found) : WordOpaque found := by
  induction path generalizing cell with
  | nil => cases read; exact opaqueCell
  | cons index rest ih =>
    cases opaqueCell with
    | boolean _ | number _ | shared _ | owned _ => simp only [Heap.fields, reduceCtorEq] at read
    | node different children =>
      simp only [Heap.fields, bind, Option.bind_eq_some_iff] at read
      obtain ⟨child, selected, tail⟩ := read
      exact ih (children child (List.mem_of_getElem? selected)) tail

theorem Graph.word_not_opaque {memory : Memory} {cell : Cell} {word : BalancedWord} {reads : List Nat}
    (graph : Graph memory cell (encodeWord word) reads) : ¬ WordOpaque cell := by
  cases word <;> cases graph with
  | node fields => intro impossible; cases impossible with | node different _ => exact different rfl

theorem Graph.word_reads_not_opaque {memory : Memory} {cell : Cell} {word : BalancedWord} {reads : List Nat}
    (graph : Graph memory cell (encodeWord word) reads) :
    ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
  induction word generalizing cell reads with
  | Empty => cases graph with | node fields => cases fields; simp
  | Pair head tail ihHead ihTail =>
    cases graph with
    | node fields => cases fields with
      | cons first rest => cases first with
        | owned headRead headGraph => cases rest with
          | cons second last => cases second with
            | owned tailRead tailGraph =>
              cases last
              intro address member raw memoryRead
              simp only [List.append_nil, List.mem_append, List.mem_singleton] at member
              rcases member with (headMember | headRoot) | (tailMember | tailRoot)
              · exact ihHead headGraph address headMember raw memoryRead
              · subst address
                have same := Option.some.inj (headRead.symm.trans memoryRead)
                subst raw
                exact headGraph.word_not_opaque
              · exact ihTail tailGraph address tailMember raw memoryRead
              · subst address
                have same := Option.some.inj (tailRead.symm.trans memoryRead)
                subst raw
                exact tailGraph.word_not_opaque

theorem Graph.shared_word_reads {memory : Memory} {pointer : Pointer} {word : BalancedWord} {reads : List Nat}
    (graph : Graph memory (.shared pointer) (.reference (encodeWord word)) reads) :
    ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
  cases graph with
  | @shared _ childCell _ _ read child =>
    intro address member raw memoryRead opaqueCell
    rcases List.mem_append.mp member with childMember | root
    · exact child.word_reads_not_opaque address childMember raw memoryRead opaqueCell
    · have same : address = pointer.root := List.mem_singleton.mp root
      subst address
      have selected : Heap.fields raw pointer.path = some childCell := by
        simpa only [Heap.read, memoryRead, bind, Option.bind] using read
      exact child.word_not_opaque (opaqueCell.fields selected)

mutual
  inductive WordLoans : Slot → Prop where
    | empty : WordLoans .empty
    | boolean (value : Bool) : WordLoans (.boolean value)
    | number (value : Nat) : WordLoans (.number value)
    | shared (word : BalancedWord) : WordLoans (.shared (encodeWord word))
    | node {kind : Kind} {tag : Nat} {parts : List Slot} : WordLoanFields parts → WordLoans (.node kind tag parts)
    | owned {part : Slot} : WordLoans part → WordLoans (.boxed part)
  inductive WordLoanFields : List Slot → Prop where
    | nil : WordLoanFields []
    | cons {part : Slot} {parts : List Slot} : WordLoans part → WordLoanFields parts → WordLoanFields (part :: parts)
end

mutual
  theorem WordLoans.of_closed {part : Slot} {ty : Ty} (typed : SlotTyped part ty) (closed : Borrow.Closed ty) : WordLoans part := by
    cases typed with
    | empty _ => exact .empty
    | boolean value => exact .boolean value
    | number _ => exact .number _
    | shared _ => cases closed
    | owned child => cases closed with | owned inner => exact .owned (WordLoans.of_closed child inner)
    | node shape fields => exact .node (WordLoanFields.of_closed fields (Borrow.shape_closed shape closed))
  termination_by sizeOf part
  theorem WordLoanFields.of_closed {parts : List Slot} {types : List Ty}
      (typed : FieldsSlotTyped parts types) (closed : Borrow.ClosedFields types) : WordLoanFields parts := by
    cases typed with
    | nil => exact .nil
    | cons first rest => cases closed with
      | cons head tail => exact .cons (WordLoans.of_closed first head) (WordLoanFields.of_closed rest tail)
  termination_by sizeOf parts
end

mutual
  theorem BorrowFootprint.word_cells {memory : Memory} {cell : Cell} {part : Slot} {loans : List Nat}
      (borrowed : BorrowFootprint memory cell part loans) (words : WordLoans part) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
    cases borrowed with
    | empty _ | boolean _ | number _ => simp
    | shared graph => cases words with | shared word => exact graph.shared_word_reads
    | node fields => cases words with | node children => exact fields.word_cells children
    | owned _ child => cases words with | owned inner => exact child.word_cells inner
  termination_by sizeOf part
  theorem BorrowFields.word_cells {memory : Memory} {cells : List Cell} {parts : List Slot} {loans : List Nat}
      (borrowed : BorrowFields memory cells parts loans) (words : WordLoanFields parts) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
    cases borrowed with
    | nil => simp
    | cons first rest => cases words with
      | cons head tail =>
        intro address member raw read
        rcases List.mem_append.mp member with left | right
        · exact first.word_cells head address left raw read
        · exact rest.word_cells tail address right raw read
  termination_by sizeOf parts
end

namespace Storage

theorem LocalResources.word_cells {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (represented : LocalResources world frame roots state slot r) (words : WordLoans (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ WordOpaque raw := by
  cases represented with
  | vacant _ _ => simp
  | stored _ _ _ resource _ => exact resource.borrowed.word_cells words

theorem Inventory.word_cells {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (inventory : Inventory world frame roots state slots r)
    (words : ∀ slot ∈ slots, WordLoans (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ WordOpaque raw := by
  induction inventory with
  | nil => simp
  | @cons slot slots head tail first rest ih =>
    intro address member raw read
    rcases List.mem_append.mp member with left | right
    · exact first.word_cells (words slot (by simp)) address left raw read
    · exact ih (fun index member => words index (List.mem_cons_of_mem _ member)) address right raw read

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
