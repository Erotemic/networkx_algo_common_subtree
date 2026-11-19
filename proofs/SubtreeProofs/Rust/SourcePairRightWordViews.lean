module

public import SubtreeProofs.Rust.SourcePairRightPrefix
public import SubtreeProofs.Rust.SourceSupportedReborrow

/-! Construct the seven actual right-call view instructions. Original view 91
borrows the left query; fresh views 93/92 borrow the owned right word in 85.
Their precise loan support remains separate from the original query family. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_word_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : RightConcatScope lh lt rh rt heads tails left table total active)
    (count : 94 ≤ active.count) (unbound : ∀ slot ∈ [90, 91, 92, 93], active.roots slot = none) :
    ∃ final after anchor,
      Calling.Prefix callee callers (rightCode 22) ((rightActions.drop 15).take 7) world active final after ∧
      AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor final after ∧
      RightConcatScope lh lt rh rt heads tails left table total after ∧
      after.state 91 = .shared (encodeWord (.Pair lh lt)) ∧
      after.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      after.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      after.state 90 = .empty ∧
      (∃ binding, after.roots 90 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      (∀ slot ∈ [90, 91, 92, 93], ∃ binding, after.roots slot = some binding) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [90, 91, 92, 93] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w90, a90, run90, m90, roots90, count90, frame90, empty90, raw90, memory90⟩ :=
    original_open_local_complete h callee (rightCode 16) (slot := 90) (by decide) (by omega) (unbound 90 (by simp))
  have originalLeft : a90.state.read (.deref (.local 1)) = some (encodeWord (.Pair lh lt)) := by
    have value : a90.state 1 = .shared (encodeWord (.Pair lh lt)) :=
      (run90.retained_local_same_calls (index := 1) (by decide +kernel) (by decide +kernel)).trans scope.payload.held.queries.left
    simp only [Partial.Locals.read, splitPlace, List.nil_append, value, Slot.read, Slot.get,
      Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨w91, a91, run91, m91, roots91, count91, frame91, value91, memory91⟩ :=
    original_borrow_view_complete m90 callee (rightCode 18) (slot := 1) (destination := 91)
      (place := .deref (.local 1)) (by simp) (by decide) rfl
      (by have value := (run90.retained_local_same_calls (index := 1) (by decide +kernel) (by decide +kernel)).trans scope.payload.held.queries.left
          rw [value]; exact .shared _ _) originalLeft (NativeData.word _)
      (by rw [count90]; omega) (by simpa [roots90, Roots.set] using unbound 91 (by simp))
  obtain ⟨w92, a92, run92, m92, roots92, count92, frame92, empty92, raw92, memory92⟩ :=
    original_open_local_complete m91 callee (rightCode 19) (slot := 92) (by decide) (by rw [count91, count90]; omega)
      (by simpa [roots91, roots90, Roots.set] using unbound 92 (by simp))
  obtain ⟨w93, a93, run93, m93, roots93, count93, frame93, empty93, raw93, memory93⟩ :=
    original_open_local_complete m92 callee (rightCode 20) (slot := 93) (by decide) (by rw [count92, count91, count90]; omega)
      (by simpa [roots92, roots91, roots90, Roots.set] using unbound 93 (by simp))
  have first3 : Calling.Prefix callee callers (rightCode 18) ((rightActions.drop 15).take 3) world active w91 a91 :=
    Calling.Prefix.append (suffix := rightCode 18) (rest := (rightActions.drop 16).take 2) run90 run91
  have first4 : Calling.Prefix callee callers (rightCode 19) ((rightActions.drop 15).take 4) world active w92 a92 :=
    Calling.Prefix.append (suffix := rightCode 19) (rest := [.storageLive 92]) first3 run92
  have first5 : Calling.Prefix callee callers (rightCode 20) ((rightActions.drop 15).take 5) world active w93 a93 :=
    Calling.Prefix.append (suffix := rightCode 20) (rest := [.storageLive 93]) first4 run93
  have value93 : a93.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) :=
    (first5.closed_local_same_calls (index := 85) (by rw [scope.wordValue]; exact ofValue_typed (word_typed _)) (.adt .word)
      (by decide +kernel)).trans scope.wordValue
  obtain ⟨_, frame⟩ := m93.native.valid.2
  obtain ⟨anchor, _, owning⟩ := frame.inspectSlot 85
  have anchored := AnchoredLoanMachine.of_original m93 owning value93 (by rw [count93, count92, count91, count90]; omega)
  let p93 := a93.forgetRefs (rightCode 20)
  have mp93 := anchored.prepare (rightCode 20)
  have root93 : p93.roots 93 = some ⟨w92.memory.length, w92.memory.length⟩ := by simp [p93, roots93, Roots.set, Activation.forgetRefs]
  have wordP93 : p93.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) := mp93.value
  have read85 : p93.state.read (.local 85) = some (encodeWord (OrderedSolver.appendWord rh rt)) := by
    simp only [Partial.Locals.read, splitPlace, wordP93, Slot.read, Slot.get, Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨pointer93, assigned93, ma, rawAssigned93⟩ := mp93.assign_owned_view (destination := 93) (by decide) (by decide) rfl read85 (NativeData.word _)
    root93 raw93 (LoanEnding.forget_empty _ _ empty93)
  let wa := w93.write w92.memory.length (.shared pointer93)
  let aa : Activation := {p93 with state := p93.state.set 93 (.shared (encodeWord (OrderedSolver.appendWord rh rt)))}
  change AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [93] 85
    (OrderedSolver.appendWord rh rt) anchor wa aa at ma
  have runA : Calling.Prefix callee callers (rightCode 21) [.assign 93 (.address (.local 85))] w93 a93 wa aa :=
    .cons (Calling.instruction_noncall_run (act := .assign 93 (.address (.local 85))) assigned93) (.nil _ _)
  let p92 := aa.forgetRefs (rightCode 21)
  have mp92 := ma.prepare (rightCode 21)
  have valueA : aa.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) := by simp only [aa, Partial.Locals.set, ite_true]
  have valueP : p92.state 93 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) :=
    (Activation.forgetRefs_observed aa (rightCode 21) 93 (by decide +kernel)).trans valueA
  have root92 : p92.roots 92 = some ⟨w91.memory.length, w91.memory.length⟩ := by
    simp [p92, aa, p93, roots93, roots92, Roots.set, Activation.forgetRefs]
  have root92a93 : a93.roots 92 = some ⟨w91.memory.length, w91.memory.length⟩ := by simp [roots93, roots92, Roots.set]
  have raw92a93 : w93.memory[w91.memory.length]? = some (.node .tuple 0 []) :=
    memory93 92 ⟨w91.memory.length, w91.memory.length⟩ (by simp [roots92, Roots.set]) _ raw92
  have raw92wa : wa.memory[w91.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp93.native.valid root93 root92a93 (by decide) raw92a93 (.shared pointer93)
  have empty92a93 : a93.state 92 = .empty :=
    (run93.unshared_local_same_calls (index := 92) (by rw [empty92]; simp) (by decide +kernel)).trans empty92
  have empty92p : p92.state 92 = .empty := by
    apply LoanEnding.forget_empty
    change (p93.state.set 93 (.shared (encodeWord (OrderedSolver.appendWord rh rt)))) 92 = .empty
    simp only [Partial.Locals.set, show (92 : Nat) ≠ 93 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty92a93
  have source92 : p92.state.read (.deref (.local 93)) = some (encodeWord (OrderedSolver.appendWord rh rt)) := by
    simp only [Partial.Locals.read, splitPlace, List.nil_append, valueP, Slot.read, Slot.get, Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨pointer92, assigned92, machine, rawAssigned92⟩ := mp92.assign_supported_view (slot := 93) (destination := 92)
    (by simp) (by decide) (by decide) rfl (by rw [valueP]; exact .shared _ _)
    source92 (NativeData.word _) root92 raw92wa empty92p
  let final := wa.write w91.memory.length (.shared pointer92)
  let after : Activation := {p92 with state := p92.state.set 92 (.shared (encodeWord (OrderedSolver.appendWord rh rt)))}
  have runB : Calling.Prefix callee callers (rightCode 22) [.assign 92 (.address (.deref (.local 93)))] wa aa final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 92 (.address (.deref (.local 93)))) assigned92) (.nil _ _)
  have last2 : Calling.Prefix callee callers (rightCode 22) ((rightActions.drop 20).take 2) w93 a93 final after :=
    Calling.Prefix.append (suffix := rightCode 22) (rest := [.assign 92 (.address (.deref (.local 93)))]) runA runB
  have whole : Calling.Prefix callee callers (rightCode 22) ((rightActions.drop 15).take 7) world active final after :=
    Calling.Prefix.append (suffix := rightCode 22) (rest := (rightActions.drop 20).take 2) first5 last2
  have rootsAfter : after.roots = a93.roots := rfl
  have sameRoot : ∀ slot, slot ∉ [90, 91, 92, 93] → after.roots slot = active.roots slot := by
    intro slot outside
    have different : slot ≠ 90 ∧ slot ≠ 91 ∧ slot ≠ 92 ∧ slot ≠ 93 := by simpa using outside
    simp only [rootsAfter, roots93, roots92, roots91, roots90, Roots.set, different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  have heldAfter := scope.payload.held.through_prefix whole
    (by intro slot member
        simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [rightActions, keepsRoot])
  have bound90 : after.roots 90 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsAfter, roots93, roots92, roots91, roots90, Roots.set]
  have root90p93 : p93.roots 90 = some ⟨world.memory.length, world.memory.length⟩ := bound90
  have raw90a93 : w93.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    memory93 90 ⟨world.memory.length, world.memory.length⟩ (by simp [roots92, roots91, roots90, Roots.set]) _
      (memory92 90 ⟨world.memory.length, world.memory.length⟩ (by simp [roots91, roots90, Roots.set]) _
        (memory91 90 ⟨world.memory.length, world.memory.length⟩ (by simp [roots90, Roots.set]) _ raw90))
  have raw90wa : wa.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp93.native.valid root93 root90p93 (by decide) raw90a93 (.shared pointer93)
  have raw90final : final.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp92.native.valid root92 (by simpa [p92, aa, Activation.forgetRefs] using root90p93)
      (by decide) raw90wa (.shared pointer92)
  have rest6 : Calling.Prefix callee callers (rightCode 22) ((rightActions.drop 16).take 6) w90 a90 final after :=
    Calling.Prefix.append (suffix := rightCode 22) (rest := (rightActions.drop 20).take 2)
      (Calling.Prefix.append (suffix := rightCode 20) (rest := [.storageLive 93])
        (Calling.Prefix.append (suffix := rightCode 19) (rest := [.storageLive 92]) run91 run92) run93) last2
  refine ⟨final, after, anchor, whole, machine, ?_, ?_, by simp [after, Partial.Locals.set], ?_,
    (rest6.unshared_local_same_calls (index := 90) (by rw [empty90]; simp) (by decide +kernel)).trans empty90,
    ⟨_, bound90, raw90final⟩, ?_, count93.trans (count92.trans (count91.trans count90)), frame93.trans (frame92.trans (frame91.trans frame90)), sameRoot, ?_⟩
  · refine ⟨⟨heldAfter, ?_⟩, machine.value, ?_, ?_⟩
    · exact (whole.closed_local_same_calls (index := 75) (by rw [scope.payload.tableValue]; exact ofValue_typed (table_typed table))
        (.adt .table) (by decide +kernel)).trans scope.payload.tableValue
    · obtain ⟨binding, root⟩ := scope.wordBound
      exact ⟨binding, by rw [sameRoot 85 (by decide)]; exact root⟩
    · intro slot member
      rw [sameRoot slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> decide)]
      exact scope.retired slot member
  · have last4 : Calling.Prefix callee callers (rightCode 22) ((rightActions.drop 18).take 4) w91 a91 final after :=
      Calling.Prefix.append (suffix := rightCode 22) (rest := (rightActions.drop 20).take 2)
        (Calling.Prefix.append (suffix := rightCode 20) (rest := [.storageLive 93]) run92 run93) last2
    exact (last4.retained_local_same_calls (index := 91) (by decide +kernel) (by decide +kernel)).trans value91
  · simpa only [after, Partial.Locals.set, show (93 : Nat) ≠ 92 by decide, ite_false] using valueP
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [rootsAfter, roots93, roots92, roots91, roots90, Roots.set]
  · intro slot binding root raw memoryRead
    have outside : slot ∉ [90, 91, 92, 93] := by intro member; rw [unbound slot member] at root; cases root
    have other92 : 92 ≠ slot := by intro same; subst slot; exact outside (by simp)
    have other93 : 93 ≠ slot := by intro same; subst slot; exact outside (by simp)
    have other90 : slot ≠ 90 := by intro same; subst slot; exact outside (by simp)
    have at90 : a90.roots slot = some binding := by simpa only [roots90, Roots.set, other90, ite_false] using root
    have other91 : slot ≠ 91 := by intro same; subst slot; exact outside (by simp)
    have at91 : a91.roots slot = some binding := by simpa only [roots91, Roots.set, other91, ite_false] using at90
    have at92 : a92.roots slot = some binding := by simpa only [roots92, Roots.set, Ne.symm other92, ite_false] using at91
    have atP93 : p93.roots slot = some binding := by
      change a93.roots slot = some binding
      rw [← rootsAfter, sameRoot slot outside]; exact root
    have atP92 : p92.roots slot = some binding := atP93
    exact Evaluator.Activation.write_other_root mp92.native.valid root92 atP92 other92
      (Evaluator.Activation.write_other_root mp93.native.valid root93 atP93 other93
        (memory93 slot binding at92 raw (memory92 slot binding at91 raw (memory91 slot binding at90 raw (memory90 slot binding root raw memoryRead))))
        (.shared pointer93)) (.shared pointer92)

end SubtreeProofs.Rust.SourceEval.Evaluator
