module

public import SubtreeProofs.Rust.SourceOriginalBorrowView
public import SubtreeProofs.Rust.SourceReadPartition

/-! Local loan support may name current owned data as well as original data.
Support is an actual local inventory with an address predicate; selected root
permissions require exclusion of that root, rather than a newer global bound. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem LocalResources.borrow_source {world : World} {active : Activation} {slot : Nat} {resources : Resources}
    (h : LocalResources world active.frame active.roots active.state slot resources)
    {place : Place} {path : List Projection} (split : splitPlace place = (slot, path))
    {value : Value} (source : active.state.read place = some value) :
    ∃ pointer reads, borrow world active.roots place = some (.shared pointer) ∧
      Graph world.memory (.shared pointer) (.reference value) reads ∧ reads ⊆ resources.reads := by
  have sourceSlot : (active.state slot).read path = some value := by
    simpa only [Partial.Locals.read, split] using source
  cases h with
  | vacant root empty =>
    cases path with
    | nil => simp [empty, Slot.read, Slot.get, Slot.materialize] at sourceSlot
    | cons projection rest => cases projection <;> simp [empty, Slot.read, Slot.get] at sourceSlot
  | @stored binding cell parts root memory classified payload alive =>
    have readRoot : Heap.read world.memory ⟨binding.address, []⟩ = some cell := by
      simp only [Heap.read, memory, bind, Option.bind, Heap.fields]
    obtain ⟨found, pointer, used, located, read, graph, included⟩ := payload.graph.read _ readRoot path sourceSlot
    have live : world.live pointer.root = true := alive _ (included (List.mem_append_right _ (by simp)))
    refine ⟨pointer, used ++ [pointer.root], ?_, .shared read graph, included⟩
    simp only [borrow, locate, split, root, memory, located, bind, Option.bind, live, ite_true]

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def LoanSupport (world : World) (active : Activation) (allowed : Nat → Prop) (slot : Nat) : Prop :=
  ∃ resources, LocalResources world active.frame active.roots active.state slot resources ∧
    ∀ address ∈ resources.loans, allowed address

namespace LoanSupport

theorem allows {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) {resources : Resources}
    (represented : LocalResources world active.frame active.roots active.state slot resources) :
    ∀ address ∈ resources.loans, allowed address := by
  obtain ⟨initial, original, support⟩ := h
  rw [← original.unique represented]
  exact support

theorem weaken {world : World} {active : Activation} {allowed larger : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) (included : ∀ address, allowed address → larger address) :
    LoanSupport world active larger slot := by
  obtain ⟨resources, represented, support⟩ := h
  exact ⟨resources, represented, fun address member => included address (support address member)⟩

theorem of_closed {world : World} {active : Activation} (valid : active.Valid world) (allowed : Nat → Prop) (slot : Nat)
    {ty : Ty} (typed : SlotTyped (active.state slot) ty) (closed : Borrow.Closed ty) : LoanSupport world active allowed slot := by
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot slot
  refine ⟨resources, represented, ?_⟩
  rw [represented.closed_loans typed closed]
  simp

theorem of_shared_graph {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (valid : active.Valid world) {binding : Binding} {pointer : Pointer} {value : Value} {loans : List Nat}
    (root : active.roots slot = some binding) (raw : world.memory[binding.address]? = some (.shared pointer))
    (initialized : active.state slot = .shared value)
    (graph : Graph world.memory (.shared pointer) (.reference value) loans) (support : ∀ address ∈ loans, allowed address) :
    LoanSupport world active allowed slot := by
  obtain ⟨_, frame⟩ := valid.2
  obtain ⟨resources, _, represented⟩ := frame.inspectSlot slot
  refine ⟨resources, represented, ?_⟩
  cases represented with
  | vacant missing _ => rw [root] at missing; cases missing
  | @stored actual cell parts actualRoot memory classified payload alive =>
    cases Option.some.inj (actualRoot.symm.trans root)
    cases Option.some.inj (memory.symm.trans raw)
    have borrowed := payload.borrowed
    rw [initialized] at borrowed
    change ∀ address ∈ parts.loans, allowed address
    generalize equation : parts.loans = actualLoans at borrowed ⊢
    cases borrowed with
    | shared other => rw [other.guards_unique graph]; exact support

theorem congr {world : World} {active after : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) (frame : after.frame = active.frame)
    (root : after.roots slot = active.roots slot) (mask : after.state slot = active.state slot) : LoanSupport world after allowed slot := by
  obtain ⟨resources, represented, support⟩ := h
  refine ⟨resources, ?_, support⟩
  rw [frame]
  exact represented.congr_at root mask

theorem transport {world final : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot)
    (kept : ∀ resources, LocalResources world active.frame active.roots active.state slot resources → Preserves world final resources.reads) :
    LoanSupport final active allowed slot := by
  obtain ⟨resources, represented, support⟩ := h
  exact ⟨resources, represented.transport (kept resources represented), support⟩

theorem clear {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) : LoanSupport world {active with state := active.state.set slot .empty} allowed slot := by
  obtain ⟨resources, represented, _⟩ := h
  obtain ⟨after, cleared, empty⟩ := represented.clear
  refine ⟨after, cleared, ?_⟩
  rw [empty]
  simp

theorem prepare {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) (code : Code) : LoanSupport world (active.forgetRefs code) allowed slot := by
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
  · exact h.congr rfl rfl same
  · apply h.clear.congr (after := active.forgetRefs code) rfl rfl
    change LoanEnding.forget code (List.range active.count) active.state slot = (active.state.set slot .empty) slot
    simpa only [Partial.Locals.set, ite_true] using empty

theorem allocate {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (h : LoanSupport world active allowed slot) (hw : world.WellFormed) (kind : Class) (cell : Cell) :
    LoanSupport (world.allocate kind cell) active allowed slot :=
  h.transport (fun resources _ => (world.allocate_keeps hw kind cell resources.reads).preserves)

end LoanSupport

theorem LoanOrigin.support {world : World} {active : Activation} {limit slot : Nat}
    (h : LoanOrigin world active limit slot) : LoanSupport world active (· < limit) slot := h

end SubtreeProofs.Rust.SourceEval.Addressed
