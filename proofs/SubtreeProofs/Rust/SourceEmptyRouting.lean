module

public import SubtreeProofs.Rust.SourceEmptyBranch

/-! Select the shared empty branch through the actual native left/right word
inspections. An early return bypasses each retained switch continuation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_cases_complete {before world final : World} {active initial after : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : MissScope initial left right table world active)
    (hempty : left = .Empty ∨ right = .Empty) {packet : ValueCell} {work : Cost}
    (branch : Calling.exec callee callers emptyLeft world active = some (.returned final after packet, work)) :
    ∃ cost, Calling.exec callee callers missCases world active = some (.returned final after packet, cost) := by
  obtain ⟨inspectLeft, inspectRight, _, _⟩ := miss_switch_native h scope
  cases left with
  | Empty =>
    refine ⟨(Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 0))).weight)).plus work, ?_⟩
    rw [missCases, Calling.exec_switch, inspectLeft]
    simp only [wordKey, Control.selectSource, Control.selectIndex, ite_true, branch, bind, Option.bind]
  | Pair head tail =>
    have rightEmpty : right = .Empty := by rcases hempty with impossible | empty; cases impossible; exact empty
    subst right
    have rightRun : Calling.exec callee callers rightCases world active =
        some (.returned final after packet, (Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 1))).weight)).plus work) := by
      rw [rightCases, Calling.exec_switch, inspectRight, emptyRight_eq_emptyLeft]
      simp only [wordKey, Control.selectSource, Control.selectIndex, ite_true, branch, bind, Option.bind]
    refine ⟨(Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 0))).weight)).plus
      ((Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 1))).weight)).plus work), ?_⟩
    rw [missCases, Calling.exec_switch, inspectLeft]
    simp [wordKey, Control.selectSource, Control.selectIndex, rightRun]

end SubtreeProofs.Rust.SourceEval.Evaluator
