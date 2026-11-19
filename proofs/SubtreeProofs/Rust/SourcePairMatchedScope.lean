module

public import SubtreeProofs.Rust.SourcePairMatchedEmbedding

/-! Construct the first thirty actual successful-root-score instructions:
extract the total, allocate both Boxes, assemble the native matched embedding,
and retire all moved-out construction temporaries before concatenation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem resultWordHole_boxes_zero (edges : Aeneas.Std.U32) : (resultWordHole edges).dropWork.boxes = 0 := by
  simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus]

theorem pair_matched_scope_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootScoreScope heads tails table subtotal world active) (total : Aeneas.Std.U32)
    (success : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (count : 71 ≤ active.count) (unbound : ∀ slot ∈ [61, 64, 65, 66, 67, 68, 69, 70], active.roots slot = none) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails table total after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot ∈ [59, 61, 65, 66, 67, 68, 69, 70], after.roots slot = none) ∧
      (∀ slot, slot ∉ [59, 64, 65, 66, 67, 68, 69, 70] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, slot ≠ 58 → slot ≠ 59 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) world active final after := by
  let callee := Helpers.callee 0 0
  have native : checkedAdd32 subtotal.val 1 = some total.val := by
    have equation := checkedAdd32_native subtotal 1#u32
    rw [success] at equation
    exact equation
  obtain ⟨wp, ap, totalRun, mp, scopeP, rootsP, countP, frameP, memoryP⟩ :=
    pair_matched_total_complete h callee scope total native (by omega) (unbound 61 (by simp))
  obtain ⟨fuel, budget, wb, ab, mb, scopeB, countB, frameB, rootsB, memoryB, stableB⟩ :=
    pair_matched_boxes_complete mp scopeP (by rw [countP]; omega)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> simpa [rootsP, Roots.set] using unbound _ (by simp))
  obtain ⟨ww, aw, wordRun, mw, scopeW, rootsW, countW, frameW, memoryW⟩ := pair_matched_word_complete mb callee scopeB
  have unbound70 : aw.roots 70 = none := by
    rw [rootsW]
    simp only [Roots.set]
    rw [rootsB 70 (by decide), rootsP]
    simpa [Roots.set] using unbound 70 (by simp)
  obtain ⟨final, after, embeddingRun, machine, finalScope, rootsAfter, countAfter, frameAfter, memoryAfter⟩ :=
    pair_matched_embedding_complete mw callee scopeW (by rw [countW, countB, countP]; exact count) unbound70
  have last12 : Calling.Prefix callee callers (matchedCode 30) ((matchedActions.drop 18).take 12) wb ab final after :=
    Calling.Prefix.append (suffix := matchedCode 30) (rest := (matchedActions.drop 23).take 7) wordRun embeddingRun
  refine ⟨fuel, budget, final, after, machine, finalScope, countAfter.trans (countW.trans (countB.trans countP)),
    frameAfter.trans (frameW.trans (frameB.trans frameP)), ?_, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [rootsAfter, rootsW]; simp only [Roots.set]; rw [rootsB 59 (by decide), rootsP]; simp [Roots.set]
    · rw [rootsAfter, rootsW]; simp only [Roots.set]; rw [rootsB 61 (by decide), rootsP]; simpa [Roots.set] using unbound 61 (by simp)
    · exact finalScope.retired 65 (by simp)
    · rw [rootsAfter]; simpa [Roots.set] using scopeW.retired 66 (by simp)
    · rw [rootsAfter, rootsW]; simp only [Roots.set]; exact scopeB.retired 67 (by simp)
    · rw [rootsAfter]; simpa [Roots.set] using scopeW.retired 68 (by simp)
    · rw [rootsAfter, rootsW]; simp only [Roots.set]; exact scopeB.retired 69 (by simp)
    · exact finalScope.retired 70 (by simp)
  · intro slot outside
    have different : slot ≠ 59 ∧ slot ≠ 64 ∧ slot ≠ 65 ∧ slot ≠ 66 ∧ slot ≠ 67 ∧ slot ≠ 68 ∧ slot ≠ 69 ∧ slot ≠ 70 := by simpa using outside
    rw [rootsAfter, rootsW]
    simp only [Roots.set, different.2.2.1, different.2.2.2.1, different.2.2.2.2.2.1, ite_false]
    rw [rootsB slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto), rootsP]
    simp only [Roots.set, different.1, ite_false]
  · intro slot binding not58 not59 root raw memoryRead
    have old : slot ∉ [61, 64, 65, 66, 67, 68, 69, 70] := by
      intro member; rw [unbound slot member] at root; cases root
    have not64 : slot ≠ 64 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at old; tauto
    have not65 : slot ≠ 65 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at old; tauto
    have not66 : slot ≠ 66 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at old; tauto
    have not68 : slot ≠ 68 := by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at old; tauto
    have root_ap : ap.roots slot = some binding := by simpa only [rootsP, Roots.set, not59, ite_false] using root
    have root_ab : ab.roots slot = some binding := by
      rw [rootsB slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at old ⊢; tauto)]; exact root_ap
    have root_aw : aw.roots slot = some binding := by simpa only [rootsW, Roots.set, not66, not68, ite_false] using root_ab
    exact memoryAfter slot binding not64 root_aw _ (memoryW slot binding not65 root_ab _ (memoryB slot binding root_ap _ (memoryP slot binding not58 root _ memoryRead)))
  · intro largerFuel largerBudget fuelBound budgetBound
    have last24 : Calling.Prefix (Recursive.original largerBudget largerFuel) callers (matchedCode 30)
        ((matchedActions.drop 6).take 24) wp ap final after :=
      Calling.Prefix.append (suffix := matchedCode 30) (rest := (matchedActions.drop 18).take 12)
        (stableB largerFuel largerBudget fuelBound budgetBound) (last12.noncall_callee _ (by decide +kernel))
    exact Calling.Prefix.append (suffix := matchedCode 30) (rest := (matchedActions.drop 6).take 24)
      (totalRun.noncall_callee _ (by decide +kernel)) last24

end SubtreeProofs.Rust.SourceEval.Evaluator
