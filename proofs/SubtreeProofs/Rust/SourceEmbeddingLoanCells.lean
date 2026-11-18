module

public import SubtreeProofs.Rust.SourceWordLoanCells

/-! Native embedding referents expose only their inline word, scalar score and
word-owned descendants. The same word-opaque cells exclude both query-word and
embedding loans, while table-owned entries can still contain borrowed words. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap verified_ordered_core

theorem Graph.result_not_opaque {memory : Memory} {cell : Cell} {result : CommonEmbedding} {reads : List Nat}
    (graph : Graph memory cell (encodeResult result) reads) : ¬ WordOpaque cell := by
  simp only [encodeResult] at graph
  cases graph with
  | node fields => cases fields with
    | cons word rest =>
      intro opaqueCell
      cases opaqueCell with
      | node _ children => exact word.word_not_opaque (children _ (by simp))

theorem Graph.result_reads_not_opaque {memory : Memory} {cell : Cell} {result : CommonEmbedding} {reads : List Nat}
    (graph : Graph memory cell (encodeResult result) reads) :
    ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
  simp only [encodeResult] at graph
  cases graph with
  | node fields => cases fields with
    | cons word rest => cases rest with
      | cons number last => cases number with
        | number _ =>
          cases last
          simpa only [List.append_nil] using word.word_reads_not_opaque

theorem Graph.shared_result_reads {memory : Memory} {pointer : Pointer} {result : CommonEmbedding} {reads : List Nat}
    (graph : Graph memory (.shared pointer) (.reference (encodeResult result)) reads) :
    ∀ address ∈ reads, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
  cases graph with
  | @shared _ childCell _ _ read child =>
    intro address member raw memoryRead opaqueCell
    rcases List.mem_append.mp member with childMember | root
    · exact child.result_reads_not_opaque address childMember raw memoryRead opaqueCell
    · have same : address = pointer.root := List.mem_singleton.mp root
      subst address
      have selected : Heap.fields raw pointer.path = some childCell := by
        simpa only [Heap.read, memoryRead, bind, Option.bind] using read
      exact child.result_not_opaque (opaqueCell.fields selected)

theorem Graph.table_opaque {memory : Memory} {cell : Cell} {table : MemoTable} {reads : List Nat}
    (graph : Graph memory cell (encodeTable table) reads) : WordOpaque cell := by
  cases table with
  | Empty =>
    cases graph with
    | node fields => cases fields; exact .node (by decide) (by intro cell member; cases member)
  | Entry entry tail =>
    cases graph with
    | node fields => cases fields with
      | cons first rest => cases first with
        | owned _ _ => cases rest with
          | cons second last => cases second with
            | owned _ _ =>
              cases last
              apply WordOpaque.node (by decide)
              intro cell member
              simp only [List.mem_cons, List.not_mem_nil, or_false] at member
              rcases member with rfl | rfl <;> exact .owned _

inductive MemoReferent : Value → Prop where
  | word (word : BalancedWord) : MemoReferent (encodeWord word)
  | result (result : CommonEmbedding) : MemoReferent (encodeResult result)

mutual
  inductive MemoLoans : Slot → Prop where
    | empty : MemoLoans .empty
    | boolean (value : Bool) : MemoLoans (.boolean value)
    | number (value : Nat) : MemoLoans (.number value)
    | shared {value : Value} : MemoReferent value → MemoLoans (.shared value)
    | node {kind : Kind} {tag : Nat} {parts : List Slot} : MemoLoanFields parts → MemoLoans (.node kind tag parts)
    | owned {part : Slot} : MemoLoans part → MemoLoans (.boxed part)
  inductive MemoLoanFields : List Slot → Prop where
    | nil : MemoLoanFields []
    | cons {part : Slot} {parts : List Slot} : MemoLoans part → MemoLoanFields parts → MemoLoanFields (part :: parts)
end

mutual
  theorem MemoLoans.of_closed {part : Slot} {ty : Ty} (typed : SlotTyped part ty) (closed : Borrow.Closed ty) : MemoLoans part := by
    cases typed with
    | empty _ => exact .empty
    | boolean value => exact .boolean value
    | number _ => exact .number _
    | shared _ => cases closed
    | owned child => cases closed with | owned inner => exact .owned (MemoLoans.of_closed child inner)
    | node shape fields => exact .node (MemoLoanFields.of_closed fields (Borrow.shape_closed shape closed))
  termination_by sizeOf part
  theorem MemoLoanFields.of_closed {parts : List Slot} {types : List Ty}
      (typed : FieldsSlotTyped parts types) (closed : Borrow.ClosedFields types) : MemoLoanFields parts := by
    cases typed with
    | nil => exact .nil
    | cons first rest => cases closed with
      | cons head tail => exact .cons (MemoLoans.of_closed first head) (MemoLoanFields.of_closed rest tail)
  termination_by sizeOf parts
end

mutual
  theorem BorrowFootprint.memo_cells {memory : Memory} {cell : Cell} {part : Slot} {loans : List Nat}
      (borrowed : BorrowFootprint memory cell part loans) (data : MemoLoans part) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
    cases borrowed with
    | empty _ | boolean _ | number _ => simp
    | shared graph => cases data with
      | shared referent => cases referent with
        | word _ => exact graph.shared_word_reads
        | result _ => exact graph.shared_result_reads
    | node fields => cases data with | node children => exact fields.memo_cells children
    | owned _ child => cases data with | owned inner => exact child.memo_cells inner
  termination_by sizeOf part
  theorem BorrowFields.memo_cells {memory : Memory} {cells : List Cell} {parts : List Slot} {loans : List Nat}
      (borrowed : BorrowFields memory cells parts loans) (data : MemoLoanFields parts) :
      ∀ address ∈ loans, ∀ raw, memory[address]? = some raw → ¬ WordOpaque raw := by
    cases borrowed with
    | nil => simp
    | cons first rest => cases data with
      | cons head tail =>
        intro address member raw read
        rcases List.mem_append.mp member with left | right
        · exact first.memo_cells head address left raw read
        · exact rest.memo_cells tail address right raw read
  termination_by sizeOf parts
end

namespace Storage

theorem LocalResources.memo_cells {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (represented : LocalResources world frame roots state slot r) (data : MemoLoans (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ WordOpaque raw := by
  cases represented with
  | vacant _ _ => simp
  | stored _ _ _ resource _ => exact resource.borrowed.memo_cells data

theorem Inventory.memo_cells {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (inventory : Inventory world frame roots state slots r)
    (data : ∀ slot ∈ slots, MemoLoans (state slot)) :
    ∀ address ∈ r.loans, ∀ raw, world.memory[address]? = some raw → ¬ WordOpaque raw := by
  induction inventory with
  | nil => simp
  | @cons slot slots head tail first rest ih =>
    intro address member raw read
    rcases List.mem_append.mp member with left | right
    · exact first.memo_cells (data slot (by simp)) address left raw read
    · exact ih (fun index member => data index (List.mem_cons_of_mem _ member)) address right raw read

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
