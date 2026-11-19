module

public import SubtreeProofs.Rust.SourceWordLoanCells
public import SubtreeProofs.Rust.SourceQueryMachine

/-! Selected fresh stack roots with word-opaque raw cells are safe against all
current word loans and preserved older callers. This includes table roots and
reference-only tuples without banning aliases with their owned descendants. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem WordLoans.safe {part : Slot} (h : WordLoans part) : LoanSafe part := by
    cases h with
    | empty => exact .empty
    | boolean value => exact .boolean value
    | number value => exact .number value
    | shared word => exact .shared (NativeData.word word)
    | node fields => exact .node fields.safe
    | owned inner => exact .owned inner.safe
  termination_by sizeOf part
  theorem WordLoanFields.safe {parts : List Slot} (h : WordLoanFields parts) : LoanSafeFields parts := by
    cases h with
    | nil => exact .nil
    | cons first rest => exact .cons first.safe rest.safe
  termination_by sizeOf parts
end

end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def WordLoanState (state : State) : Prop := ∀ slot, WordLoans (state slot)

theorem WordLoanState.set {state : State} (h : WordLoanState state) (slot : Nat) {part : Slot} (words : WordLoans part) :
    WordLoanState (state.set slot part) := by
  intro index
  by_cases same : index = slot
  · subst index; simpa only [Partial.Locals.set, ite_true] using words
  · simpa only [Partial.Locals.set, same, ite_false] using h index

theorem WordLoanState.clear {state : State} (h : WordLoanState state) (slot : Nat) : WordLoanState (state.set slot .empty) :=
  h.set slot .empty

theorem WordLoanState.prepare {state : State} (h : WordLoanState state) (code : Code) (slots : List Nat) :
    WordLoanState (LoanEnding.forget code slots state) := by
  intro index
  rcases LoanEnding.forget_eq_or_empty code slots state index with same | empty
  · rw [same]; exact h index
  · rw [empty]; exact .empty

theorem Derived.RootLoansAllowed.of_word_preserved {before world : World} {active : Activation} {callers : List Activation}
    {slot : Nat} {binding : Binding} {previous : Resources} {cell : Cell}
    (words : WordLoanState active.state) (memory : world.memory[binding.address]? = some cell) (opaqueCell : WordOpaque cell)
    (view : Callers before callers previous) (hw : before.WellFormed) (kept : Preserves before world previous.reads)
    (fresh : before.memory.length ≤ binding.address) : Derived.RootLoansAllowed world active callers slot binding := by
  intro remainder suspended remaining callers forbidden
  rcases List.mem_append.mp forbidden with current | old
  · exact remaining.word_cells (fun index _ => words index) binding.address current cell memory opaqueCell
  · have bound := view.preserved_read_bound hw kept callers binding.address (callers.loans_subset_reads old)
    omega

theorem allowed_inline_word_opaque {before world : World} {active : Activation} {callers : List Activation}
    {previous current suspended : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (words : WordLoanState active.state)
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
  · exact scanned.inventory.word_cells (fun index _ => words index) binding.address currentLoan rootCell memory opaqueCell
  · have new := h.fresh _ binding hb
    have old := h.previousCallers.preserved_read_bound h.beforeWellFormed h.kept callerView binding.address oldRead
    omega

end SubtreeProofs.Rust.SourceEval.Addressed
