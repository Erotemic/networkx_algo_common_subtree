module

public import SubtreeProofs.Rust.SourcePairRightScope

/-! Construct the remaining twenty-one actual right-contraction instructions
from the owned right concatenation through the native optional-result switch. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_from_concat_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    {lh lt rh rt : BalancedWord} {heads tails leftWitness : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (scope : RightConcatScope lh lt rh rt heads tails leftWitness table total active)
    (count : 96 ≤ active.count) (future : ∀ slot, 88 ≤ slot → active.roots slot = none)
    (childTotal : NativeTotal (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    ∃ minimumFuel minimumBudget viewsWorld viewsActive argumentWorld argumentActive callWorld callActive final after result output cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairRightScope lh lt rh rt heads tails leftWitness total result output final after ∧
      memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) table = .ok (result, output) ∧
      Derived.scrutinee final after callers (.discriminant (.local 88)) = some (lookupKey result, after) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, 96 ≤ slot → after.roots slot = none) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 22) ((rightActions.drop 15).take 7) world active viewsWorld viewsActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 24) ((rightActions.drop 22).take 2) viewsWorld viewsActive argumentWorld argumentActive ∧
        Derived.call (Recursive.original budget fuel) argumentWorld (argumentActive.forgetRefs (rightCode 24)) callers
          .evaluate rightContractionArgs 90 = some (callWorld, callActive, cost) ∧
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 25) [.call .evaluate rightContractionArgs 90] argumentWorld argumentActive callWorld callActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases ((rightActions.drop 25).take 11) callWorld callActive final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases (rightActions.drop 15) world active final after := by
  obtain ⟨viewsWorld, viewsActive, anchor, views, mv, scopeV, leftV, rightV, intermediateV, empty90, root90, _, countV, frameV, rootsV, _⟩ :=
    pair_right_word_views_complete h (Helpers.callee 0 0) scope (by omega)
      (by intro slot member; exact future slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega))
  obtain ⟨fuel, budget, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter, frameAfter, _, _, stable⟩ :=
    pair_right_scope_complete mv scopeV leftV rightV intermediateV empty90 root90 (by rw [countV]; exact count)
      (by intro slot member
          rw [rootsV slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; omega)]
          exact future slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega)) childTotal
  obtain ⟨arguments, called, callRun, cleanup, remaining14⟩ := stable fuel budget (by rfl) (by rfl)
  have whole : Calling.Prefix (Recursive.original budget fuel) callers rightContractionCases (rightActions.drop 15) world active final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 22).take 14)
      (views.noncall_callee _ (by decide +kernel)) remaining14
  refine ⟨fuel, budget, viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, final, after, result, output, cost,
    machine, scopeAfter, native, inspection, countAfter.trans countV, frameAfter.trans frameV, ?_, ?_⟩
  · intro slot above
    rw [whole.root_above above (by decide +kernel)]
    exact future slot (by omega)
  · intro largerFuel largerBudget fuelBound budgetBound
    obtain ⟨arguments, called, callRun, cleanup, remaining14⟩ := stable largerFuel largerBudget fuelBound budgetBound
    have viewsRun := views.noncall_callee (Recursive.original largerBudget largerFuel) (by decide +kernel)
    exact ⟨viewsRun, arguments, called, callRun, cleanup,
      Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 22).take 14) viewsRun remaining14⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
