module

public import SubtreeProofs.Rust.SourcePairMatchedBoxes
public import SubtreeProofs.Rust.SourceOriginalAggregate

/-! Assemble the matched native pair word from the two actual owned Boxes,
then drop/retire the moved-out Box temporaries without destroying their owners. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure MatchedWordScope (heads tails : CommonEmbedding) (table : MemoTable) (total : Aeneas.Std.U32)
    (world : World) (active : Activation) : Prop where
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  totalValue : active.state 58 = .number total.val
  wordValue : active.state 65 = Slot.ofValue (encodeWord (.Pair heads.word tails.word))
  candidateEmpty : active.state 64 = .empty
  candidateRoot : ∃ binding, active.roots 64 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  retired : ∀ slot ∈ [66, 68], active.roots slot = none

theorem pair_matched_word_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedBoxesScope heads tails table total world active) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 23) ((matchedActions.drop 18).take 5) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedWordScope heads tails table total final after ∧ after.roots = (active.roots.set 68 none).set 66 none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 65 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨root65, bound65, raw65⟩ := scope.wordRoot
  obtain ⟨wa, aa, assigned, ma, rootsA, countA, frameA, empty66, empty68, wordA, closedA, memoryA⟩ :=
    original_aggregate_two_complete h callee (matchedCode 19) 66 68 65 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (.boxed (encodeWord heads.word)) (.boxed (encodeWord tails.word)) scope.headBox scope.tailBox
      .word 1 (word_typed (.Pair heads.word tails.word)) (.adt .word) bound65 raw65 scope.wordEmpty
  obtain ⟨root66, bound66⟩ := scope.headBoxRoot
  obtain ⟨root68, bound68⟩ := scope.tailBoxRoot
  have plan : RetirementPlan aa.roots ((matchedActions.drop 19).take 4) ((aa.roots.set 68 none).set 66 none) :=
    .drop (by rw [rootsA]; exact bound68) (.dead (by rw [rootsA]; exact bound68)
      (.drop (binding := root66) (by simpa [rootsA, Roots.set] using bound66)
        (.dead (binding := root66) (by simpa [rootsA, Roots.set] using bound66) (.nil _))))
  have zero : ZeroRetirement ((matchedActions.drop 19).take 4) aa.state := by
    intro slot member
    have selected : slot = 68 ∨ slot = 66 := by simpa [matchedActions] using member
    rcases selected with rfl | rfl
    · rw [empty68]; simp only [Slot.dropWork]
    · rw [empty66]; simp only [Slot.dropWork]
  obtain ⟨final, after, retired, machine, rootsAfter, countAfter, memoryAfter⟩ := plan.complete_original callee (matchedCode 23) ma rfl zero
  have whole : Calling.Prefix callee callers (matchedCode 23) ((matchedActions.drop 18).take 5) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 23) (rest := (matchedActions.drop 19).take 4) assigned retired
  have kept : ∀ slot ∈ [37, 47, 42, 58, 64], ∀ ty, SlotTyped (active.state slot) ty → Borrow.Closed ty → after.state slot = active.state slot := by
    intro slot member ty typed closed
    have different : slot ≠ 66 ∧ slot ≠ 68 ∧ slot ≠ 65 := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl <;> decide
    have same := closedA slot different.1 different.2.1 different.2.2 ty typed closed
    exact (retired.closed_local_same (index := slot) ma.native.valid ma.native.callersValid ma.native.wellFormed
      (by rw [same]; exact typed) closed (by decide +kernel)
      (by simp [matchedActions, LocalPreservation.action, different.1, different.2.1])).trans same
  refine ⟨final, after, whole, machine, ?_, ?_, countAfter.trans countA,
    (retired.frame_count ma.native.valid ma.native.callersValid ma.native.wellFormed (by decide +kernel)).1.trans frameA, ?_⟩
  · refine ⟨(kept 37 (by simp) (.adt .embedding) (by rw [scope.headHole]; exact resultWordHole_typed heads.edges) (.adt .embedding)).trans scope.headHole,
      (kept 47 (by simp) (.adt .embedding) (by rw [scope.tailHole]; exact resultWordHole_typed tails.edges) (.adt .embedding)).trans scope.tailHole,
      (kept 42 (by simp) (.adt .table) (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table)).trans scope.tableValue,
      (kept 58 (by simp) .u32 (by rw [scope.totalValue]; exact .number total.hmax) .u32).trans scope.totalValue, ?_,
      (kept 64 (by simp) .u32 (by rw [scope.candidateEmpty]; exact .empty _) .u32).trans scope.candidateEmpty, ?_, ?_⟩
    · have value : aa.state 65 = Slot.ofValue (encodeWord (.Pair heads.word tails.word)) := wordA
      exact (retired.closed_local_same (index := 65) ma.native.valid ma.native.callersValid ma.native.wellFormed
        (by rw [value]; exact ofValue_typed (word_typed (.Pair heads.word tails.word))) (.adt .word)
        (by decide +kernel) (by decide +kernel)).trans value
    · obtain ⟨root64, bound64, raw64⟩ := scope.candidateRoot
      exact ⟨root64, by simpa [rootsAfter, rootsA, Roots.set] using bound64,
        by rw [memoryAfter]; exact memoryA 64 root64 (by decide) bound64 _ raw64⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [rootsAfter, Roots.set]
  · rw [rootsAfter, rootsA]
  · intro slot binding different root raw memoryRead
    rw [memoryAfter]; exact memoryA slot binding different root raw memoryRead

end SubtreeProofs.Rust.SourceEval.Evaluator
