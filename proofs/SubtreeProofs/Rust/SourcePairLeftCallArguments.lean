module

public import SubtreeProofs.Rust.SourcePairLeftWordViewsEntry
public import SubtreeProofs.Rust.SourceAnchoredPrefixes
public import SubtreeProofs.Rust.SourceMatchedCandidateScope

/-! Construct the actual right-query and owned-table arguments of the left
contraction call while retaining its freshly anchored left word view. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure LeftContractionArgumentScope (left right : BalancedWord) (table : MemoTable) (world : World) (active : Activation) : Prop where
  left : active.state 77 = .shared (encodeWord left)
  right : active.state 79 = .shared (encodeWord right)
  tableValue : active.state 80 = Slot.ofValue (encodeTable table)
  tableMoved : active.state 42 = .empty
  resultEmpty : active.state 76 = .empty
  result : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  bound : ∀ slot ∈ [76, 77, 79, 80], ∃ binding, active.roots slot = some binding

theorem pair_left_call_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor world active)
    (callee : Derived.Callees) (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (left : active.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)))
    (empty76 : active.state 76 = .empty)
    (root76 : ∃ binding, active.roots 76 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 81 ≤ active.count) (unbound : ∀ slot ∈ [79, 80], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 48) ((matchedActions.drop 44).take 4) world active final after ∧
      AnchoredLoanMachine before callers previous external [79, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [77, 78] 71 (OrderedSolver.appendWord lh lt) anchor final after ∧
      LeftContractionArgumentScope (OrderedSolver.appendWord lh lt) (.Pair rh rt) table final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedCandidateScope heads tails total after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [79, 80] → after.roots slot = active.roots slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have sourceRight : active.state.read (.deref (.local 2)) = some (encodeWord (.Pair rh rt)) := by
    simp only [Partial.Locals.read, splitPlace, List.nil_append, queries.right, Slot.read, Slot.get,
      Slot.materialize_ofValue, bind, Option.bind]
  obtain ⟨wr, ar, runR, mr, rootsR, countR, frameR, rightR, memoryR⟩ :=
    anchored_original_borrow_complete h callee (matchedCode 46) (slot := 2) (destination := 79)
      (by simp) (by decide) (by decide) rfl (by rw [queries.right]; exact .shared _ _)
      sourceRight (NativeData.word _) (by omega) (unbound 79 (by simp))
  have tableR : ar.state 42 = Slot.ofValue (encodeTable table) :=
    (runR.closed_local_same_calls (index := 42) (by rw [candidate.tableValue]; exact ofValue_typed (table_typed table))
      (.adt .table) (by decide +kernel)).trans candidate.tableValue
  obtain ⟨final, after, runT, machine, rootsT, countT, frameT, moved42, tableAfter, memoryT⟩ :=
    anchored_move_view_complete mr callee (matchedCode 48) (source := 42) (destination := 80)
      (by decide) (by decide) (by decide) (by decide) tableR (table_typed table) (.adt .table)
      (by rw [countR]; omega) (by simpa [rootsR, Roots.set] using unbound 80 (by simp))
  have whole : Calling.Prefix callee callers (matchedCode 48) ((matchedActions.drop 44).take 4) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 48) (rest := (matchedActions.drop 46).take 2) runR runT
  have queryAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete whole queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have candidateAfter := candidate.candidate_scope.through_prefix whole
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [matchedActions, keepsRoot])
  have sameRoot : ∀ slot, slot ∉ [79, 80] → after.roots slot = active.roots slot := by
    intro slot outside
    have different : slot ≠ 79 ∧ slot ≠ 80 := by simpa using outside
    simp only [rootsT, rootsR, Roots.set, different.1, different.2, ite_false]
  have leftAfter : after.state 77 = .shared (encodeWord (OrderedSolver.appendWord lh lt)) :=
    (whole.retained_local_same_calls (index := 77) (by decide +kernel) (by decide +kernel)).trans left
  have rightAfter : after.state 79 = .shared (encodeWord (.Pair rh rt)) :=
    (runT.retained_local_same_calls (index := 79) (by decide +kernel) (by decide +kernel)).trans rightR
  obtain ⟨binding76, bound76, raw76⟩ := root76
  have bound76r : ar.roots 76 = some binding76 := by simpa [rootsR, Roots.set] using bound76
  refine ⟨final, after, whole, machine, ⟨leftAfter, rightAfter, tableAfter, moved42,
    (whole.closed_local_same_calls (index := 76) (by rw [empty76]; exact .empty .u32) .u32 (by decide +kernel)).trans empty76,
    ⟨binding76, by rw [sameRoot 76 (by decide)]; exact bound76,
      memoryT 76 binding76 bound76r _ (memoryR 76 binding76 bound76 _ raw76)⟩, ?_⟩,
    queryAfter, candidateAfter, countT.trans countR, frameT.trans frameR, sameRoot, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨binding76, by rw [sameRoot 76 (by decide)]; exact bound76⟩
    · exact Activation.root_of_materialize machine.native.valid (value := .reference (encodeWord (OrderedSolver.appendWord lh lt)))
        (by rw [leftAfter]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize machine.native.valid (value := .reference (encodeWord (.Pair rh rt)))
        (by rw [rightAfter]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize machine.native.valid (by rw [tableAfter]; exact Slot.materialize_ofValue _)
  · intro slot binding root raw memoryRead
    have outside : slot ∉ [79, 80] := by intro member; rw [unbound slot member] at root; cases root
    have boundR : ar.roots slot = some binding := by
      have other : slot ≠ 79 := by intro same; subst slot; exact outside (by simp)
      simpa only [rootsR, Roots.set, other, ite_false] using root
    exact memoryT slot binding boundR raw (memoryR slot binding root raw memoryRead)

end SubtreeProofs.Rust.SourceEval.Evaluator
