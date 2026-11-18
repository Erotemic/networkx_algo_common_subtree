module

public import SubtreeProofs.Rust.SourcePairRootScoreArguments

/-! Execute the actual root-score checked-add with its literal operand, then
retire the scalar argument. Native overflow remains an explicit result case. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rootScoreArgs : List Operand := [.move (.local 60), .number 1]

theorem root_score_arguments_source {state : State} (subtotal : Nat) (value : state 60 = .number subtotal) :
    SourceEval.operands state rootScoreArgs = some ([.number subtotal, .number 1], state.set 60 .empty) := by
  have one := move_local_source (state := state) (slot := 60) (value := .number subtotal) (by rw [value]; simp only [Slot.materialize])
  have two : SourceEval.operand (state.set 60 .empty) (.number 1) = some (.number 1, state.set 60 .empty) := by
    simp [SourceEval.operand]
  simp only [rootScoreArgs, SourceEval.operands, one, two, bind, Option.bind]

structure RootScoreScope (heads tails : CommonEmbedding) (table : MemoTable) (subtotal : Aeneas.Std.U32)
    (world : World) (active : Activation) : Prop where
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  subtotalValue : active.state 51 = .number subtotal.val
  result : active.state 59 = Slot.ofValue (encodeNumberOption (checkedAdd32 subtotal.val 1))
  resultRoot : ∃ binding, active.roots 59 = some binding
  totalEmpty : active.state 58 = .empty
  totalRoot : ∃ binding, active.roots 58 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  retired : ∀ slot ∈ [52, 55, 60], active.roots slot = none

theorem pair_root_score_call_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootScoreArgumentScope heads tails table subtotal world active) (count : 61 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootScoreScope heads tails table subtotal final after ∧ after.roots = active.roots.set 60 none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 59 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases (rootScoreActions.drop 10) world active final after := by
  let observed := active.forgetRefs (rootScoreCode 10)
  have machine := h.prepare (rootScoreCode 10)
  have value60 : observed.state 60 = .number subtotal.val := (h.prepare_closed_local _ 60 (by decide)).trans scope.argument
  obtain ⟨root59, bound59, raw59⟩ := scope.resultRoot
  have empty59 : observed.state 59 = .empty := LoanEnding.forget_empty _ _ scope.resultEmpty
  obtain ⟨fuel, budget, wc, ac, mc, rootsC, countC, frameC, stateC, memoryC, stable⟩ :=
    original_checked_add_operands_complete machine rootScoreArgs
      (by intro op member; simp only [rootScoreArgs, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl <;> trivial)
      (destination := 59) (by decide)
      (by intro index member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> change _ < active.count <;> omega)
      subtotal.val 1 subtotal.hmax (by decide) (root_score_arguments_source subtotal.val value60)
      (machine.native.safe.clear 60) (machine.closed.clear 60)
      (by intro index member; left
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Partial.Locals.set])
      bound59 raw59 (by simpa only [Partial.Locals.set, show (59 : Nat) ≠ 60 by decide, ite_false] using empty59)
  have oldMasks : ∀ slot, slot ≠ 59 → slot ≠ 60 → ac.state slot = observed.state slot := by
    intro slot not59 not60
    simp only [stateC, Partial.Locals.set, not59, not60, ite_false, observed]
  obtain ⟨root60, bound60⟩ := scope.argumentRoot
  have plan : RetirementPlan ac.roots [.storageDead 60] (ac.roots.set 60 none) :=
    .dead (by rw [rootsC]; exact bound60) (.nil _)
  have zero : ZeroRetirement [.storageDead 60] ac.state := by
    intro slot member
    have same : slot = 60 := by simpa using member
    subst slot; simp [stateC, Partial.Locals.set, Slot.dropWork]
  let callee := Helpers.callee 0 0
  obtain ⟨final, after, retirement, finalMachine, rootsAfter, countAfter, memoryAfter⟩ :=
    plan.complete_original callee rootScoreCases mc rfl zero
  refine ⟨fuel, budget, final, after, finalMachine, ?_, ?_, countAfter.trans countC, ?_, ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_, ⟨root59, ?_⟩, ?_, ?_, ?_⟩
    · have value : ac.state 37 = Slot.ofValue (encodeResult heads) :=
        (oldMasks 37 (by decide) (by decide)).trans ((h.prepare_closed_local _ 37 (by decide)).trans scope.headValue)
      exact (retirement.closed_local_same (index := 37) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 47 = Slot.ofValue (encodeResult tails) :=
        (oldMasks 47 (by decide) (by decide)).trans ((h.prepare_closed_local _ 47 (by decide)).trans scope.tailValue)
      exact (retirement.closed_local_same (index := 47) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 42 = Slot.ofValue (encodeTable table) :=
        (oldMasks 42 (by decide) (by decide)).trans ((h.prepare_closed_local _ 42 (by decide)).trans scope.tableValue)
      exact (retirement.closed_local_same (index := 42) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 51 = .number subtotal.val :=
        (oldMasks 51 (by decide) (by decide)).trans ((h.prepare_closed_local _ 51 (by decide)).trans scope.subtotalValue)
      exact (retirement.closed_local_same (index := 51) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact .number subtotal.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans value
    · have value : ac.state 59 = Slot.ofValue (encodeNumberOption (checkedAdd32 subtotal.val 1)) := by simp [stateC, Partial.Locals.set]
      exact (retirement.closed_local_same (index := 59) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact ofValue_typed (Types.checkedAdd32_typed _ _)) (.option .u32) (by decide +kernel) (by decide +kernel)).trans value
    · simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set] using bound59
    · have value : ac.state 58 = .empty :=
        (oldMasks 58 (by decide) (by decide)).trans (LoanEnding.forget_empty _ _ scope.totalEmpty)
      exact (retirement.closed_local_same (index := 58) mc.native.valid mc.native.callersValid mc.native.wellFormed
        (by rw [value]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans value
    · obtain ⟨root58, bound58, raw58⟩ := scope.totalRoot
      exact ⟨root58, by simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set] using bound58,
        by rw [memoryAfter]; exact memoryC 58 root58 (by decide) bound58 _ raw58⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl
      · simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set] using scope.retired 52 (by simp)
      · simpa [rootsAfter, rootsC, Activation.forgetRefs, Roots.set] using scope.retired 55 (by simp)
      · simp [rootsAfter, Roots.set]
  · rw [rootsAfter, rootsC]; rfl
  · exact (retirement.frame_count mc.native.valid mc.native.callersValid mc.native.wellFormed (by decide +kernel)).1.trans frameC
  · intro slot binding different root raw memoryRead
    rw [memoryAfter]; exact memoryC slot binding different root raw memoryRead
  · intro largerFuel largerBudget fuelBound budgetBound
    have callRun : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (rootScoreCode 11)
        [.call .checkedAdd rootScoreArgs 59] world active wc ac :=
      .cons (Calling.instruction_call_run (stable largerFuel largerBudget fuelBound budgetBound)) (.nil _ _)
    exact Calling.Prefix.append (suffix := rootScoreCases) (rest := [.storageDead 60]) callRun
      (retirement.noncall_callee _ (by decide +kernel))

end SubtreeProofs.Rust.SourceEval.Evaluator
