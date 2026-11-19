module

public import SubtreeProofs.Rust.SourceEmbeddingLoanCells

/-! Native word and embedding references exclude selected word-opaque stack
roots. In particular, insertion can move its owned table argument while the
original query tuple and a temporary embedding view still hold shared loans. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

def MemoLoanState (state : State) : Prop := ∀ slot, MemoLoans (state slot)

theorem MemoLoanState.set {state : State} (h : MemoLoanState state) (slot : Nat) {part : Slot} (data : MemoLoans part) :
    MemoLoanState (state.set slot part) := by
  intro index
  by_cases same : index = slot
  · subst index; simpa only [Partial.Locals.set, ite_true] using data
  · simpa only [Partial.Locals.set, same, ite_false] using h index

theorem MemoLoanState.clear {state : State} (h : MemoLoanState state) (slot : Nat) : MemoLoanState (state.set slot .empty) :=
  h.set slot .empty

theorem MemoLoanState.prepare {state : State} (h : MemoLoanState state) (code : Code) (slots : List Nat) :
    MemoLoanState (LoanEnding.forget code slots state) := by
  intro index
  rcases LoanEnding.forget_eq_or_empty code slots state index with same | empty
  · rw [same]; exact h index
  · rw [empty]; exact .empty

theorem allowed_inline_memo_opaque {before world : World} {active : Activation} {callers : List Activation}
    {previous current suspended : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (data : MemoLoanState active.state)
    (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {place : Place} (inlinePlace : InlinePlace place)
    (raw : ∀ binding, active.roots (splitPlace place).1 = some binding →
      ∃ cell, world.memory[binding.address]? = some cell ∧ WordOpaque cell) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move place) := by
  intro cell pointer located forbidden
  obtain ⟨binding, hb, same⟩ := locate_inline_root inlinePlace located
  obtain ⟨rootCell, memory, opaqueCell⟩ := raw binding hb
  rw [same] at forbidden
  rcases List.mem_append.mp forbidden with currentLoan | oldRead
  · exact scanned.inventory.memo_cells (fun index _ => data index) binding.address currentLoan rootCell memory opaqueCell
  · have new := h.fresh _ binding hb
    have old := h.previousCallers.preserved_read_bound h.beforeWellFormed h.kept callerView binding.address oldRead
    omega

theorem allowed_table_local {before world : World} {active : Activation} {callers : List Activation}
    {previous current suspended : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (data : MemoLoanState active.state)
    (scanned : Scanned world active current) (callerView : Callers world callers suspended)
    {slot : Nat} {table : MemoTable} (initialized : active.state slot = Slot.ofValue (encodeTable table)) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  apply allowed_inline_memo_opaque (place := .local slot) h data scanned callerView trivial
  intro binding hb
  change active.roots slot = some binding at hb
  obtain ⟨_, frame⟩ := h.valid.2
  obtain ⟨cell, used, memory, _, graph, _⟩ := frame.get hb
  have full : Graph world.memory cell (encodeTable table) used :=
    graph.materialize (by rw [initialized]; exact Slot.materialize_ofValue _)
  exact ⟨cell, memory, full.table_opaque⟩

end SubtreeProofs.Rust.SourceEval.Addressed
