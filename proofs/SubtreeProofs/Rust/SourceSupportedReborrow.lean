module

public import SubtreeProofs.Rust.SourceAnchoredStorage

/-! Reborrowing through a supported shared reference retains its precise loan
support. The intermediate reference's stack root is excluded from the new view. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem LoanSupport.borrow_shared {world : World} {active : Activation} {allowed : Nat → Prop} {slot : Nat}
    (origin : LoanSupport world active allowed slot) {path : List Projection} (route : SharedRoute (active.state slot) path)
    {place : Place} (split : splitPlace place = (slot, path)) {value : Value} (source : active.state.read place = some value) :
    ∃ pointer reads, Storage.borrow world active.roots place = some (.shared pointer) ∧
      Graph world.memory (.shared pointer) (.reference value) reads ∧ (∀ address ∈ reads, allowed address) := by
  obtain ⟨resources, represented, supported⟩ := origin
  cases represented with
  | vacant root empty => rw [empty] at route; cases route
  | @stored binding cell parts root memory classified payload alive =>
    have readRoot : Heap.read world.memory ⟨binding.address, []⟩ = some cell := by
      simp only [Heap.read, memory, bind, Option.bind, Heap.fields]
    have sourceSlot : (active.state slot).read path = some value := by simpa only [Partial.Locals.read, split] using source
    obtain ⟨found, pointer, used, located, read, graph, included⟩ := payload.borrowed.read_shared _ readRoot route sourceSlot
    have live : world.live pointer.root = true := alive _ (List.mem_append_left _
      (payload.borrowed.subset_reads payload.graph (included (List.mem_append_right _ (by simp)))))
    refine ⟨pointer, used ++ [pointer.root], ?_, .shared read graph, fun address member => supported address (included member)⟩
    simp only [Storage.borrow, Storage.locate, split, root, memory, located, bind, Option.bind, live, ite_true]

theorem AnchoredLoanMachine.assign_supported_view {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot destination : Nat} (member : slot ∈ fresh) (outside : destination ∉ fresh ++ original) (different : source ≠ destination)
    {place : Place} {path : List Projection} (split : splitPlace place = (slot, path))
    (route : SharedRoute (active.state slot) path) {value : Value}
    (sourceValue : active.state.read place = some value) (data : NativeData value)
    {binding : Binding} (root : active.roots destination = some binding)
    (raw : world.memory[binding.address]? = some (.node .tuple 0 [])) (empty : active.state destination = .empty) :
    ∃ pointer, Derived.assign world active callers destination (.address place) =
        some (world.write binding.address (.shared pointer), {active with state := active.state.set destination (.shared value)}) ∧
      AnchoredLoanMachine before callers previous external original (destination :: fresh) source word anchor
        (world.write binding.address (.shared pointer)) {active with state := active.state.set destination (.shared value)} ∧
      (world.write binding.address (.shared pointer)).memory[binding.address]? = some (.shared pointer) := by
  obtain ⟨pointer, reads, borrow, graph, supported⟩ := (h.supportedLoans slot member).borrow_shared route split sourceValue
  exact ⟨pointer, h.assign_scoped_borrow outside different sourceValue data borrow graph supported root raw empty⟩

end SubtreeProofs.Rust.SourceEval.Addressed
