module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins
public import SubtreeProofs.Rust.SourceEvaluatorCommonEntry

/-! The constructed native lookup scope has no reference-containing locals
outside its original query slots. Unbound source locals are empty by the actual
frame invariant, rather than by a separate guessed initialization profile. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem LookupScope.closed_outside_queries {world : World} {active initial : Activation}
    {left right : BalancedWord} {table : MemoTable} (h : LookupScope initial left right table world active)
    (valid : active.Valid world) (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) :
    ClosedOutside [1, 2] active.state := by
  intro slot outside
  by_cases three : slot = 3
  · subst slot; exact ⟨.adt .table, by rw [h.inputs.table]; exact ofValue_typed (table_typed table), .adt .table⟩
  by_cases four : slot = 4
  · subst slot; exact ⟨.adt .optional, by rw [h.result]; exact ofValue_typed (option_typed _), .adt .optional⟩
  by_cases zero : slot = 0
  · subst slot; exact ⟨.u32, by rw [h.returnEmpty]; exact .empty _, .u32⟩
  by_cases six : slot = 6
  · subst slot; exact ⟨.u32, by rw [h.viewEnded]; exact .empty _, .u32⟩
  have noneRoot : active.roots slot = none := by
    by_cases retired : slot ∈ [5, 7, 8]
    · exact h.retired slot retired
    · rw [h.otherRoots slot (by simpa [zero, four, six] using retired)]
      exact unbound slot (by simpa [three] using outside)
  obtain ⟨_, frame⟩ := valid.2
  have empty : active.state slot = .empty := by simpa only [noneRoot] using frame.slots slot
  exact ⟨.u32, by rw [empty]; exact .empty _, .u32⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
