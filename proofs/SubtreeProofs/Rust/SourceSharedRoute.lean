module

public import SubtreeProofs.Rust.SourceTupleLoanOrigins
public import SubtreeProofs.Rust.SourceHeapPlaces

/-! Place reads that cross a shared reference borrow only existing loan targets.
Inline fields and owned dereferences before that crossing introduce no loan to
the starting stack root. This retains query/table aliases in recursive views. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

inductive SharedRoute : Slot → List Projection → Prop where
  | shared (value : Value) (path : List Projection) : SharedRoute (.shared value) (.deref :: path)
  | owned {part : Slot} {path : List Projection} : SharedRoute part path → SharedRoute (.boxed part) (.deref :: path)
  | field {kind : Kind} {tag : Nat} {parts : List Slot} {variant : Option Nat} {index : Nat} {part : Slot} {path : List Projection}
      (valid : variant.all (· = tag) = true) (selected : parts[index]? = some part) (tail : SharedRoute part path) :
      SharedRoute (.node kind tag parts) (.field variant index :: path)

theorem BorrowFields.get_selected {memory : Memory} {cells : List Cell} {parts : List Slot} {loans : List Nat}
    (h : BorrowFields memory cells parts loans) (index : Nat) {part : Slot} (selected : parts[index]? = some part) :
    ∃ cell used, cells[index]? = some cell ∧ BorrowFootprint memory cell part used ∧ used ⊆ loans := by
  induction index generalizing cells parts loans with
  | zero => cases h with
    | nil => cases selected
    | cons first rest => cases selected; exact ⟨_, _, rfl, first, fun _ member => List.mem_append_left _ member⟩
  | succ index ih => cases h with
    | nil => cases selected
    | cons first rest =>
      obtain ⟨cell, used, atCell, borrowed, included⟩ := ih rest selected
      exact ⟨cell, used, atCell, borrowed, fun _ member => List.mem_append_right _ (included member)⟩

theorem BorrowFootprint.read_shared {memory : Memory} {cell : Cell} {part : Slot} {loans : List Nat}
    (borrowed : BorrowFootprint memory cell part loans) (pointer : Pointer) (read : Heap.read memory pointer = some cell)
    {path : List Projection} (route : SharedRoute part path) {value : Value} (source : part.read path = some value) :
    ∃ found address used,
      locatePath memory cell pointer path = some (found, address) ∧ Heap.read memory address = some found ∧
      Graph memory found value used ∧ used ++ [address.root] ⊆ loans := by
  induction route generalizing cell loans pointer value with
  | shared referent path =>
    cases borrowed with
    | shared graph => cases graph with
      | shared atTarget targetGraph =>
        have sourceTarget : (Slot.ofValue referent).read path = some value := by
          simpa only [Slot.read, Slot.get] using source
        obtain ⟨found, address, used, located, targetRead, graph, included⟩ := targetGraph.partial.read _ atTarget path sourceTarget
        refine ⟨found, address, used, ?_, targetRead, graph, included⟩
        simpa only [locatePath, atTarget, bind, Option.bind] using located
  | @owned inner path tail ih =>
    cases borrowed with
    | @owned address child part loans atChild childBorrowed =>
      have readChild : Heap.read memory ⟨address, []⟩ = some child := by simp only [Heap.read, atChild, bind, Option.bind, Heap.fields]
      have childSource : inner.read path = some value := by simpa only [Slot.read, Slot.get] using source
      obtain ⟨found, target, used, located, targetRead, graph, included⟩ := ih childBorrowed _ readChild childSource
      refine ⟨found, target, used, ?_, targetRead, graph, included⟩
      simpa only [locatePath, atChild, bind, Option.bind] using located
  | @field kind tag parts variant index child path valid selected tail ih =>
    cases borrowed with
    | node fields =>
      obtain ⟨raw, childLoans, atChild, childBorrowed, included⟩ := fields.get_selected index selected
      have readChild : Heap.read memory (pointer.field index) = some raw := (read_field read).trans atChild
      have childSource : child.read path = some value := by
        simpa only [Slot.read, Slot.get, valid, ite_true, selected, bind, Option.bind] using source
      obtain ⟨found, target, used, located, targetRead, graph, childIncluded⟩ := ih childBorrowed _ readChild childSource
      refine ⟨found, target, used, ?_, targetRead, graph, fun _ member => included (childIncluded member)⟩
      simpa only [locatePath, valid, ite_true, atChild, bind, Option.bind] using located

end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LoanOrigin.borrow_shared {world : World} {active : Activation} {limit slot : Nat}
    (origin : LoanOrigin world active limit slot) {path : List Projection} (route : SharedRoute (active.state slot) path)
    {place : Place} (split : splitPlace place = (slot, path)) {value : Value} (source : active.state.read place = some value)
    (valid : active.Valid world) :
    ∃ pointer loans, Storage.borrow world active.roots place = some (.shared pointer) ∧
      Graph world.memory (.shared pointer) (.reference value) loans ∧ (∀ address ∈ loans, address < limit) := by
  obtain ⟨r, represented, bound⟩ := origin
  cases represented with
  | vacant root empty =>
    rw [empty] at route
    cases route
  | @stored binding cell resources atRoot memory classified payload alive =>
    have readRoot : Heap.read world.memory ⟨binding.address, []⟩ = some cell := by simp only [Heap.read, memory, bind, Option.bind, Heap.fields]
    have sourceSlot : (active.state slot).read path = some value := by simpa only [Partial.Locals.read, split] using source
    obtain ⟨found, pointer, used, located, read, graph, included⟩ := payload.borrowed.read_shared _ readRoot route sourceSlot
    have live : world.live pointer.root = true := by
      obtain ⟨_, frame⟩ := valid.2
      obtain ⟨_, _, raw, _, partialGraph, guards⟩ := frame.get atRoot
      have sameCell : _ = cell := Option.some.inj (raw.symm.trans memory)
      subst sameCell
      obtain ⟨other, address, reads, otherLocated, _, _, selectedGuards⟩ := partialGraph.read _ readRoot path sourceSlot
      have same := Prod.mk.inj (Option.some.inj (located.symm.trans otherLocated))
      obtain ⟨rfl, rfl⟩ := same
      exact frame.alive _ (guards (selectedGuards (List.mem_append_right _ (by simp))))
    refine ⟨pointer, used ++ [pointer.root], ?_, .shared read graph, fun address member => bound address (included member)⟩
    simp only [Storage.borrow, Storage.locate, split, atRoot, memory, located, bind, Option.bind, live, ite_true]

theorem LoanOrigin.of_shared_graph {world : World} {active : Activation} {limit slot : Nat}
    (valid : active.Valid world) {binding : Binding} {pointer : Pointer} {value : Value} {loans : List Nat}
    (root : active.roots slot = some binding) (raw : world.memory[binding.address]? = some (.shared pointer))
    (initialized : active.state slot = .shared value)
    (graph : Graph world.memory (.shared pointer) (.reference value) loans) (bound : ∀ address ∈ loans, address < limit) :
    LoanOrigin world active limit slot := by
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot slot
  refine ⟨resources, represented, ?_⟩
  cases represented with
  | vacant missing _ => rw [root] at missing; cases missing
  | @stored actual cell parts actualRoot memory classified payload alive =>
    have sameRoot := Option.some.inj (actualRoot.symm.trans root)
    subst actual
    have sameCell := Option.some.inj (memory.symm.trans raw)
    subst cell
    have borrowed := payload.borrowed
    rw [initialized] at borrowed
    change ∀ address ∈ parts.loans, address < limit
    generalize loanEq : parts.loans = actualLoans at borrowed ⊢
    cases borrowed with
    | shared other => rw [other.guards_unique graph]; exact bound

end SubtreeProofs.Rust.SourceEval.Addressed
