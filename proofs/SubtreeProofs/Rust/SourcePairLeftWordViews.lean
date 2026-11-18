module

public import SubtreeProofs.Rust.SourcePairLeftConcatEntry
public import SubtreeProofs.Rust.SourceSupportedReborrow

/-! Construct the first five actual contraction-call setup instructions.
References 78/77 borrow the owned concatenated word in 71; their exact loan
support is separate from the original bounded query family. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_word_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (wordValue : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)))
    (count : 79 ≤ active.count) (unbound : ∀ slot ∈ [76, 77, 78], active.roots slot = none) :
    ∃ final after anchor,
      Calling.Prefix callee callers (matchedCode 44) ((matchedActions.drop 39).take 5) world active final after ∧
      AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedScope heads tails table total after ∧
      after.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      after.state 76 = .empty ∧
      (∃ binding, after.roots 76 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      (∀ slot ∈ [76, 77, 78], ∃ binding, after.roots slot = some binding) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [76, 77, 78] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w76, a76, run76, m76, roots76, count76, frame76, empty76, raw76, memory76⟩ :=
    original_open_local_complete h callee (matchedCode 40) (slot := 76) (by decide) (by omega) (unbound 76 (by simp))
  obtain ⟨w77, a77, run77, m77, roots77, count77, frame77, empty77, raw77, memory77⟩ :=
    original_open_local_complete m76 callee (matchedCode 41) (slot := 77) (by decide) (by rw [count76]; omega)
      (by simpa [roots76, Roots.set] using unbound 77 (by simp))
  obtain ⟨w78, a78, run78, m78, roots78, count78, frame78, empty78, raw78, memory78⟩ :=
    original_open_local_complete m77 callee (matchedCode 42) (slot := 78) (by decide) (by rw [count77, count76]; omega)
      (by simpa [roots77, roots76, Roots.set] using unbound 78 (by simp))
  have first2 : Calling.Prefix callee callers (matchedCode 41) ((matchedActions.drop 39).take 2) world active w77 a77 :=
    Calling.Prefix.append (suffix := matchedCode 41) (rest := [.storageLive 77]) run76 run77
  have first3 : Calling.Prefix callee callers (matchedCode 42) ((matchedActions.drop 39).take 3) world active w78 a78 :=
    Calling.Prefix.append (suffix := matchedCode 42) (rest := [.storageLive 78]) first2 run78
  have value78 : a78.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) :=
    (first3.closed_local_same_calls (index := 71) (by rw [wordValue]; exact ofValue_typed (word_typed _)) (.adt .word)
      (by decide +kernel)).trans wordValue
  obtain ⟨_, frame⟩ := m78.native.valid.2
  obtain ⟨anchor, _, owning⟩ := frame.inspectSlot 71
  have anchored := AnchoredLoanMachine.of_original m78 owning value78 (by rw [count78, count77, count76]; omega)
  let p78 := a78.forgetRefs (matchedCode 42)
  have mp78 := anchored.prepare (matchedCode 42)
  have root78 : p78.roots 78 = some ⟨w77.memory.length, w77.memory.length⟩ := by simp [p78, roots78, Roots.set, Activation.forgetRefs]
  have wordP78 : p78.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) := mp78.value
  have read71 : p78.state.read (.local 71) = some (encodeWord (OrderedSolver.appendWord lh lt)) := by
    simp only [Partial.Locals.read, splitPlace, wordP78, Slot.read, Slot.get, Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨pointer78, assigned78, ma, rawAssigned78⟩ := mp78.assign_owned_view (destination := 78) (by decide) (by decide) rfl read71 (NativeData.word _)
    root78 raw78 (LoanEnding.forget_empty _ _ empty78)
  let wa := w78.write w77.memory.length (.shared pointer78)
  let aa : Activation := {p78 with state := p78.state.set 78 (.shared (encodeWord (OrderedSolver.appendWord lh lt)))}
  change AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] [78] 71
    (OrderedSolver.appendWord lh lt) anchor wa aa at ma
  have runA : Calling.Prefix callee callers (matchedCode 43) [.assign 78 (.address (.local 71))] w78 a78 wa aa :=
    .cons (Calling.instruction_noncall_run (act := .assign 78 (.address (.local 71))) assigned78) (.nil _ _)
  let p77 := aa.forgetRefs (matchedCode 43)
  have mp77 := ma.prepare (matchedCode 43)
  have valueA : aa.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) := by simp only [aa, Partial.Locals.set, ite_true]
  have valueP : p77.state 78 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) :=
    (Activation.forgetRefs_observed aa (matchedCode 43) 78 (by decide +kernel)).trans valueA
  have root77 : p77.roots 77 = some ⟨w76.memory.length, w76.memory.length⟩ := by
    simp [p77, aa, p78, roots78, roots77, Roots.set, Activation.forgetRefs]
  have root77a78 : a78.roots 77 = some ⟨w76.memory.length, w76.memory.length⟩ := by simp [roots78, roots77, Roots.set]
  have raw77a78 : w78.memory[w76.memory.length]? = some (.node .tuple 0 []) :=
    memory78 77 ⟨w76.memory.length, w76.memory.length⟩ (by simp [roots77, Roots.set]) _ raw77
  have raw77wa : wa.memory[w76.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp78.native.valid root78 root77a78 (by decide) raw77a78 (.shared pointer78)
  have empty77a78 : a78.state 77 = .empty :=
    (run78.unshared_local_same_calls (index := 77) (by rw [empty77]; simp) (by decide +kernel)).trans empty77
  have empty77p : p77.state 77 = .empty := by
    apply LoanEnding.forget_empty
    change (p78.state.set 78 (.shared (encodeWord (OrderedSolver.appendWord lh lt)))) 77 = .empty
    simp only [Partial.Locals.set, show (77 : Nat) ≠ 78 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty77a78
  have source77 : p77.state.read (.deref (.local 78)) = some (encodeWord (OrderedSolver.appendWord lh lt)) := by
    simp only [Partial.Locals.read, splitPlace, List.nil_append, valueP, Slot.read, Slot.get, Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨pointer77, assigned77, machine, rawAssigned77⟩ := mp77.assign_supported_view (slot := 78) (destination := 77)
    (by simp) (by decide) (by decide) rfl (by rw [valueP]; exact .shared _ _)
    source77 (NativeData.word _) root77 raw77wa empty77p
  let final := wa.write w76.memory.length (.shared pointer77)
  let after : Activation := {p77 with state := p77.state.set 77 (.shared (encodeWord (OrderedSolver.appendWord lh lt)))}
  have runB : Calling.Prefix callee callers (matchedCode 44) [.assign 77 (.address (.deref (.local 78)))] wa aa final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 77 (.address (.deref (.local 78)))) assigned77) (.nil _ _)
  have last2 : Calling.Prefix callee callers (matchedCode 44) ((matchedActions.drop 42).take 2) w78 a78 final after :=
    Calling.Prefix.append (suffix := matchedCode 44) (rest := [.assign 77 (.address (.deref (.local 78)))]) runA runB
  have whole : Calling.Prefix callee callers (matchedCode 44) ((matchedActions.drop 39).take 5) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 44) (rest := (matchedActions.drop 42).take 2) first3 last2
  have rootsAfter : after.roots = a78.roots := rfl
  have sameRoot : ∀ slot, slot ∉ [76, 77, 78] → after.roots slot = active.roots slot := by
    intro slot outside
    have different : slot ≠ 76 ∧ slot ≠ 77 ∧ slot ≠ 78 := by simpa using outside
    simp only [rootsAfter, roots78, roots77, roots76, Roots.set, different.1, different.2.1, different.2.2, ite_false]
  have queryAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete whole queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have bound76 : after.roots 76 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsAfter, roots78, roots77, roots76, Roots.set]
  have root76p78 : p78.roots 76 = some ⟨world.memory.length, world.memory.length⟩ := bound76
  have raw76a78 : w78.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    memory78 76 ⟨world.memory.length, world.memory.length⟩ (by simp [roots77, roots76, Roots.set]) _
      (memory77 76 ⟨world.memory.length, world.memory.length⟩ (by simp [roots76, Roots.set]) _ raw76)
  have raw76wa : wa.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp78.native.valid root78 root76p78 (by decide) raw76a78 (.shared pointer78)
  have raw76final : final.memory[world.memory.length]? = some (.node .tuple 0 []) :=
    Evaluator.Activation.write_other_root mp77.native.valid root77 (by simpa [p77, aa, Activation.forgetRefs] using root76p78)
      (by decide) raw76wa (.shared pointer77)
  have rest4 : Calling.Prefix callee callers (matchedCode 44) ((matchedActions.drop 40).take 4) w76 a76 final after :=
    Calling.Prefix.append (suffix := matchedCode 44) (rest := (matchedActions.drop 42).take 2)
      (Calling.Prefix.append (suffix := matchedCode 42) (rest := [.storageLive 78]) run77 run78) last2
  refine ⟨final, after, anchor, whole, machine, queryAfter, ?_, by simp [after, Partial.Locals.set], ?_,
    (rest4.unshared_local_same_calls (index := 76) (by rw [empty76]; simp) (by decide +kernel)).trans empty76,
    ⟨_, bound76, raw76final⟩, ?_, count78.trans (count77.trans count76), frame78.trans (frame77.trans frame76), sameRoot, ?_⟩
  · refine ⟨(whole.closed_local_same_calls (index := 37) (by rw [candidate.headHole]; exact resultWordHole_typed heads.edges)
        (.adt .embedding) (by decide +kernel)).trans candidate.headHole,
      (whole.closed_local_same_calls (index := 47) (by rw [candidate.tailHole]; exact resultWordHole_typed tails.edges)
        (.adt .embedding) (by decide +kernel)).trans candidate.tailHole,
      (whole.closed_local_same_calls (index := 42) (by rw [candidate.tableValue]; exact ofValue_typed (table_typed table))
        (.adt .table) (by decide +kernel)).trans candidate.tableValue,
      (whole.closed_local_same_calls (index := 58) (by rw [candidate.totalValue]; exact .number total.hmax)
        .u32 (by decide +kernel)).trans candidate.totalValue,
      (whole.closed_local_same_calls (index := 64) (by rw [candidate.candidate]; exact ofValue_typed (result_typed (matchedWitness heads tails total)))
        (.adt .embedding) (by decide +kernel)).trans candidate.candidate, ?_⟩
    intro slot member
    rw [sameRoot slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> decide)]
    exact candidate.retired slot member
  · simpa only [after, Partial.Locals.set, show (78 : Nat) ≠ 77 by decide, ite_false] using valueP
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [rootsAfter, roots78, roots77, roots76, Roots.set]
  · intro slot binding root raw memoryRead
    have outside : slot ∉ [76, 77, 78] := by intro member; rw [unbound slot member] at root; cases root
    have other77 : 77 ≠ slot := by intro same; subst slot; exact outside (by simp)
    have other78 : 78 ≠ slot := by intro same; subst slot; exact outside (by simp)
    have other76 : slot ≠ 76 := by intro same; subst slot; exact outside (by simp)
    have at76 : a76.roots slot = some binding := by simpa only [roots76, Roots.set, other76, ite_false] using root
    have at77 : a77.roots slot = some binding := by simpa only [roots77, Roots.set, Ne.symm other77, ite_false] using at76
    have atP78 : p78.roots slot = some binding := by
      change a78.roots slot = some binding
      rw [← rootsAfter, sameRoot slot outside]; exact root
    have atP77 : p77.roots slot = some binding := atP78
    exact Evaluator.Activation.write_other_root mp77.native.valid root77 atP77 other77
      (Evaluator.Activation.write_other_root mp78.native.valid root78 atP78 other78
        (memory78 slot binding at77 raw (memory77 slot binding at76 raw (memory76 slot binding root raw memoryRead)))
        (.shared pointer78)) (.shared pointer77)

end SubtreeProofs.Rust.SourceEval.Evaluator
