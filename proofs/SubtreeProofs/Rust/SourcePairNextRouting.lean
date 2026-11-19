module

public import SubtreeProofs.Rust.SourcePairHeadScopeEntry

/-! Actual native pair/pair routing preserves the completed branch's next
state through all retained joins. Costs include each real inspection and join;
parent return remains the lookup switch's separate continuation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_cases_next {before world final : World} {active initial after : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : MissScope initial (.Pair lh lt) (.Pair rh rt) table world active)
    {work : Cost} (branch : Calling.exec callee callers recurseHeads world active = some (.next final after, work)) :
    ∃ cost, Calling.exec callee callers missCases world active = some (.next final after, cost) := by
  obtain ⟨inspectLeft, inspectRight, _, _⟩ := miss_switch_native h scope
  let leftCost := ((Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 0))).weight)).plus {}).plus work
  have leftRun : Calling.exec callee callers leftPairCheck world active = some (.next final after, leftCost) := by
    rw [leftPairCheck, Calling.exec_switch, inspectLeft]
    simp only [wordKey, Control.selectSource, Control.selectIndex, ite_true, Calling.exec_done, bind, Option.bind, branch]
    rfl
  let rightCost := ((Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 1))).weight)).plus leftCost).plus {}
  have rightRun : Calling.exec callee callers rightCases world active = some (.next final after, rightCost) := by
    rw [rightCases, Calling.exec_switch, inspectRight]
    simp [wordKey, Control.selectSource, Control.selectIndex, leftRun, Calling.exec_done]
    rfl
  refine ⟨((Cost.local (1 + (Scrutinee.discriminant (.deref (.field (.local 13) none 0))).weight)).plus rightCost).plus {}, ?_⟩
  rw [missCases, Calling.exec_switch, inspectLeft]
  simp [wordKey, Control.selectSource, Control.selectIndex, rightRun, Calling.exec_done]

end SubtreeProofs.Rust.SourceEval.Evaluator
