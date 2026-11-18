module

public import SubtreeProofs.Rust.SourcePrefixLocals
public import SubtreeProofs.Rust.SourceCacheHitProgram

/-! Build the cache-hit starting invariant from the independently constructed
lookup scope and query origins. Initialized native locals provide real bound
roots; unbound non-parameter roots follow from the parsed entry convention. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Activation.root_of_materialize {world : World} {active : Activation} (h : active.Valid world)
    {slot : Nat} {value : Value} (ready : (active.state slot).materialize = some value) :
    ∃ binding, active.roots slot = some binding := by
  cases hb : active.roots slot with
  | some binding => exact ⟨binding, rfl⟩
  | none =>
    obtain ⟨_, frame⟩ := h.2
    have empty : active.state slot = .empty := by simpa only [hb] using frame.slots slot
    simp only [empty, Slot.materialize] at ready
    cases ready

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem LookupScope.query_machine {before world : World} {active initial : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat}
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (h : LoanSafeMachine before callers previous external world active)
    (origins : QueryOrigins world active before.memory.length)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) :
    QueryMachine before callers previous external world active :=
  ⟨h, scope.closed_outside_queries h.valid unbound, scope.inputs.references, origins⟩

theorem LookupScope.hit_value {world : World} {active initial : Activation}
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    {result : CommonEmbedding} (hit : (LookupEvents.lookup table left right).1 = some result) :
    active.state 4 = Slot.ofValue (encodeOption (some result)) := by
  simpa only [hit] using scope.result

theorem LookupScope.unbound_hit_local {world : World} {active initial : Activation}
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none)
    {slot : Nat} (localIndex : slot ∈ [9, 10, 11, 12]) : active.roots slot = none := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at localIndex
  rcases localIndex with rfl | rfl | rfl | rfl <;> rw [scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)

end SubtreeProofs.Rust.SourceEval.Evaluator
