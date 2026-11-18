module

public import SubtreeProofs.Rust.SourcePairScoreCall

/-! Construct all fifteen actual subtotal-prefix instructions after a native
successful tail result, including scalar copies, checked addition and cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def numberKey : Option Nat → Key
  | none => .variant .optional 0
  | some _ => .variant .optional 1

theorem number_result_scrutinee_source {state : State} {slot : Nat} {result : Option Nat}
    (initialized : state slot = Slot.ofValue (encodeNumberOption result)) :
    SourceEval.scrutinee state (.discriminant (.local slot)) = some (numberKey result, state) := by
  cases result <;> simp [SourceEval.scrutinee, splitPlace, initialized, encodeNumberOption, Slot.ofValue, Slot.get, numberKey]

theorem pair_score_scope_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : PairTailScope initial lh lt rh rt heads (some tails) table world active)
    (count : 55 ≤ active.count) (unbound : ∀ slot ∈ [48, 51, 52, 53, 54], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      ScoreSumScope heads tails table final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [51, 52, 53, 54] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 47 → slot ≠ 52 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Derived.scrutinee final after callers (.discriminant (.local 52)) =
        some (numberKey (checkedAdd32 heads.edges.val tails.edges.val), after) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨wp, ap, payload, mp, rootsP, countP, frameP, holeP, tailsP, headsP, tableP, leftP, rightP, memoryP⟩ :=
    score_tail_payload_complete h callee scope (by omega) (unbound 48 (by simp))
  obtain ⟨wa, aa, arguments, ma, scopeA, memoryA⟩ :=
    pair_score_arguments_complete mp callee headsP tailsP tableP (by rw [countP]; exact count)
      (by intro slot member; rw [rootsP]; exact unbound slot (List.mem_cons_of_mem _ member))
  obtain ⟨fuel, budget, final, after, machine, finalScope, rootsAfter, countAfter, frameAfter, memoryAfter, stable⟩ :=
    pair_score_call_complete ma scopeA (by rw [scopeA.count, countP]; exact count)
  have first12 : Calling.Prefix callee callers (scoreCode 12) (scoreActions.take 12) world active wa aa :=
    Calling.Prefix.append (suffix := scoreCode 12) (rest := (scoreActions.drop 6).take 6) payload arguments
  have inspection := Derived.scrutinee_complete machine.native.valid machine.native.callersValid _
    (number_result_scrutinee_source finalScope.result) (by intros; trivial)
  refine ⟨fuel, budget, final, after, machine, finalScope, countAfter.trans (scopeA.count.trans countP),
    frameAfter.trans (scopeA.frame.trans frameP), ?_, ?_, inspection, ?_⟩
  · intro slot outside
    have different : slot ≠ 53 ∧ slot ≠ 54 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto
    rw [rootsAfter]
    simp only [scoreArgumentsRetired, Roots.set, different.1, different.2, ite_false]
    rw [scopeA.otherRoots slot outside, rootsP]
  · intro slot binding not47 not52 root raw memoryRead
    have rootP : ap.roots slot = some binding := by rw [rootsP]; exact root
    have outside : slot ∉ [51, 52, 53, 54] := by
      intro member
      have missing := unbound slot (List.mem_cons_of_mem 48 member)
      rw [missing] at root; cases root
    have rootA : aa.roots slot = some binding := by rw [scopeA.otherRoots slot outside]; exact rootP
    exact memoryAfter slot binding not52 rootA _ (memoryA slot binding rootP _ (memoryP slot binding not47 root _ memoryRead))
  · intro largerFuel largerBudget fuelBound budgetBound
    exact Calling.Prefix.append (suffix := scoreCases) (rest := scoreActions.drop 12)
      (first12.noncall_callee _ (by decide +kernel)) (stable largerFuel largerBudget fuelBound budgetBound)

end SubtreeProofs.Rust.SourceEval.Evaluator
