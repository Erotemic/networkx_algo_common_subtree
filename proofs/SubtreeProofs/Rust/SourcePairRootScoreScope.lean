module

public import SubtreeProofs.Rust.SourcePairRootScoreCall

/-! All twelve actual root-score instructions reach the native result switch.
The subtotal is retained, both witnesses remain owned, and the updated table
and fresh total payload storage are ready for contraction or overflow cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_root_score_scope_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreSumScope heads tails table world active) (subtotal : Aeneas.Std.U32)
    (success : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (count : 61 ≤ active.count) (unbound : ∀ slot ∈ [55, 58, 59, 60], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootScoreScope heads tails table subtotal final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [52, 58, 59, 60] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ∉ [51, 52, 59] → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Derived.scrutinee final after callers (.discriminant (.local 59)) = some (numberKey (checkedAdd32 subtotal.val 1), after) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions world active final after := by
  let callee := Helpers.callee 0 0
  have native : checkedAdd32 heads.edges.val tails.edges.val = some subtotal.val := by rw [checkedAdd32_native, success]; rfl
  obtain ⟨wp, ap, copied, mp, scopeP, rootsP, countP, frameP, memoryP⟩ :=
    pair_root_subtotal_complete h callee scope subtotal native (by omega) (unbound 55 (by simp))
  obtain ⟨wa, aa, arguments, ma, scopeA, countA, frameA, rootsA, memoryA⟩ :=
    pair_root_score_arguments_complete mp callee scopeP (by rw [countP]; exact count)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> simpa [rootsP, Roots.set] using unbound _ (by simp))
  obtain ⟨fuel, budget, final, after, machine, finalScope, rootsAfter, countAfter, frameAfter, memoryAfter, stable⟩ :=
    pair_root_score_call_complete ma scopeA (by rw [countA, countP]; exact count)
  have first10 : Calling.Prefix callee callers (rootScoreCode 10) (rootScoreActions.take 10) world active wa aa :=
    Calling.Prefix.append (suffix := rootScoreCode 10) (rest := (rootScoreActions.drop 6).take 4) copied arguments
  have inspection := Derived.scrutinee_complete machine.native.valid machine.native.callersValid _
    (number_result_scrutinee_source finalScope.result) (by intros; trivial)
  refine ⟨fuel, budget, final, after, machine, finalScope, countAfter.trans (countA.trans countP),
    frameAfter.trans (frameA.trans frameP), ?_, ?_, inspection, ?_⟩
  · intro slot outside
    have different : slot ≠ 52 ∧ slot ≠ 58 ∧ slot ≠ 59 ∧ slot ≠ 60 := by simpa using outside
    rw [rootsAfter]
    simp only [Roots.set, different.2.2.2, ite_false]
    rw [rootsA slot (by simp [different.2.1, different.2.2.1, different.2.2.2]), rootsP]
    simp only [Roots.set, different.1, ite_false]
  · intro slot binding outside root raw memoryRead
    have different : slot ≠ 51 ∧ slot ≠ 52 ∧ slot ≠ 59 := by simpa using outside
    have rootP : ap.roots slot = some binding := by simpa [rootsP, Roots.set, different.2.1] using root
    have old : slot ∉ [58, 59, 60] := by
      intro member
      have missing := unbound slot (List.mem_cons_of_mem 55 member)
      rw [missing] at root; cases root
    have rootA : aa.roots slot = some binding := by rw [rootsA slot old]; exact rootP
    exact memoryAfter slot binding different.2.2 rootA _
      (memoryA slot binding rootP _ (memoryP slot binding different.1 root _ memoryRead))
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := rootScoreCases) (rest := rootScoreActions.drop 10)
      (first10.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
