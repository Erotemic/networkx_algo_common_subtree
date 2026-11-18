module

public import SubtreeProofs.Rust.SourcePairScoreArguments
public import SubtreeProofs.Rust.SourceOriginalCheckedAdd

/-! Execute the real subtotal checked-add and retire its two scalar argument
roots. Both owned witnesses and the updated memo table remain in scope. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure ScoreSumScope (heads tails : CommonEmbedding) (table : MemoTable) (world : World) (active : Activation) : Prop where
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  result : active.state 52 = Slot.ofValue (encodeNumberOption (checkedAdd32 heads.edges.val tails.edges.val))
  resultRoot : ∃ binding, active.roots 52 = some binding
  subtotalEmpty : active.state 51 = .empty
  subtotalRoot : ∃ binding, active.roots 51 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  retired : ∀ slot ∈ [53, 54], active.roots slot = none

def scoreArgumentsRetired (roots : Roots) : Roots := (roots.set 54 none).set 53 none

theorem pair_score_call_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreArgumentScope initial heads tails table world active) (count : 55 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      ScoreSumScope heads tails table final after ∧
      after.roots = scoreArgumentsRetired active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 52 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases (scoreActions.drop 12) world active final after := by
  let observed := active.forgetRefs (scoreCode 12)
  have machine := h.prepare (scoreCode 12)
  obtain ⟨root52, bound52, raw52⟩ := scope.resultRoot
  have left : observed.state 53 = .number heads.edges.val := (h.prepare_closed_local _ 53 (by decide)).trans scope.left
  have right : observed.state 54 = .number tails.edges.val := (h.prepare_closed_local _ 54 (by decide)).trans scope.right
  obtain ⟨fuel, budget, wc, ac, mc, rootsC, countC, frameC, stateC, memoryC, stable⟩ :=
    original_checked_add_complete machine 53 54 52 (by decide) (by decide) (by decide) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
      heads.edges.val tails.edges.val heads.edges.hmax tails.edges.hmax left right bound52 raw52
      (LoanEnding.forget_empty _ _ scope.resultEmpty)
  have oldMasks : ∀ slot, slot ∉ [52, 53, 54] → ac.state slot = observed.state slot := by
    intro slot outside
    have different : slot ≠ 52 ∧ slot ≠ 53 ∧ slot ≠ 54 := by simpa using outside
    simp only [stateC, numberCallMasks, Partial.Locals.set, different.1, different.2.1, different.2.2, ite_false, observed]
  obtain ⟨root53, bound53⟩ := scope.bound 53 (by simp)
  obtain ⟨root54, bound54⟩ := scope.bound 54 (by simp)
  have plan : RetirementPlan ac.roots (scoreActions.drop 13) (scoreArgumentsRetired ac.roots) :=
    .dead (by rw [rootsC]; exact bound54) (.dead (binding := root53)
      (by simpa [rootsC, Activation.forgetRefs, Roots.set] using bound53) (.nil _))
  have zero : ZeroRetirement (scoreActions.drop 13) ac.state := by
    intro slot member
    have selected : slot = 54 ∨ slot = 53 := by simpa [scoreActions] using member
    rcases selected with rfl | rfl <;> simp [stateC, numberCallMasks, Partial.Locals.set, Slot.dropWork]
  let callee := Helpers.callee 0 0
  obtain ⟨final, after, retirement, finalMachine, rootsAfter, countAfter, memoryAfter⟩ :=
    plan.complete_original callee scoreCases mc rfl zero
  have finalScope : ScoreSumScope heads tails table final after := by
    refine ⟨?_, ?_, ?_, ?_, ⟨root52, ?_⟩, ?_, ?_, ?_⟩
    · have value : ac.state 37 = Slot.ofValue (encodeResult heads) :=
        (oldMasks 37 (by decide)).trans ((h.prepare_closed_local _ 37 (by decide)).trans scope.headValue)
      exact (retirement.closed_local_same (index := 37) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 47 = Slot.ofValue (encodeResult tails) :=
        (oldMasks 47 (by decide)).trans ((h.prepare_closed_local _ 47 (by decide)).trans scope.tailValue)
      exact (retirement.closed_local_same (index := 47) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 42 = Slot.ofValue (encodeTable table) :=
        (oldMasks 42 (by decide)).trans ((h.prepare_closed_local _ 42 (by decide)).trans scope.table)
      exact (retirement.closed_local_same (index := 42) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 52 = Slot.ofValue (encodeNumberOption (checkedAdd32 heads.edges.val tails.edges.val)) := by simp [stateC, Partial.Locals.set]
      exact (retirement.closed_local_same (index := 52) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (Types.checkedAdd32_typed _ _)) (.option .u32) (by decide +kernel) (by decide +kernel)).trans value
    · simpa [rootsAfter, scoreArgumentsRetired, rootsC, Activation.forgetRefs, Roots.set] using bound52
    · have value : ac.state 51 = .empty :=
        (oldMasks 51 (by decide)).trans (LoanEnding.forget_empty _ _ scope.subtotalEmpty)
      exact (retirement.closed_local_same (index := 51) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans value
    · obtain ⟨root51, bound51, raw51⟩ := scope.subtotalRoot
      exact ⟨root51, by simpa [rootsAfter, scoreArgumentsRetired, rootsC, Activation.forgetRefs, Roots.set] using bound51,
        by rw [memoryAfter]; exact memoryC 51 root51 (by decide) bound51 _ raw51⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [rootsAfter, scoreArgumentsRetired, Roots.set]
  refine ⟨fuel, budget, final, after, finalMachine, finalScope, ?_, countAfter.trans countC, ?_, ?_, ?_⟩
  · rw [rootsAfter, rootsC]; rfl
  · exact (retirement.frame_count mc.native.valid mc.native.callersValid mc.native.wellFormed (by decide +kernel)).1.trans frameC
  · intro slot binding different root raw memoryRead
    rw [memoryAfter]; exact memoryC slot binding different root raw memoryRead
  · intro largerFuel largerBudget fuelBound budgetBound
    have callRun : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (scoreCode 13)
        [.call .checkedAdd (numberCallArgs 53 54) 52] world active wc ac :=
      .cons (Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)) (.nil _ _)
    exact Calling.Prefix.append (suffix := scoreCases) (rest := scoreActions.drop 13) callRun
      (retirement.noncall_callee _ (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
