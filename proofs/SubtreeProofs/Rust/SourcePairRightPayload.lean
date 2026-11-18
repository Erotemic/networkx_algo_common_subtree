module

public import SubtreeProofs.Rust.SourcePairRightProgram
public import SubtreeProofs.Rust.SourceOriginalOptionalPayload

/-! Extract the successful left witness into its held payload while retaining
the matched candidate, original queries and both native contraction inputs. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RightHeldScope (lh lt rh rt : BalancedWord) (heads tails left : CommonEmbedding) (total : Aeneas.Std.U32)
    (active : Activation) : Prop where
  queries : PairQueryScope lh lt rh rt active
  matched : MatchedCandidateScope heads tails total active
  leftWord : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  leftHole : active.state 74 = headPayloadHole
  leftWitness : active.state 81 = Slot.ofValue (encodeResult left)
  oldTableEmpty : active.state 42 = .empty
  retired : ∀ slot ∈ [76, 77, 78, 79, 80, 82], active.roots slot = none

structure RightPayloadScope (lh lt rh rt : BalancedWord) (heads tails left : CommonEmbedding) (table : MemoTable)
    (total : Aeneas.Std.U32) (active : Activation) : Prop where
  held : RightHeldScope lh lt rh rt heads tails left total active
  tableValue : active.state 75 = Slot.ofValue (encodeTable table)

theorem RightHeldScope.through_prefix {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {total : Aeneas.Std.U32}
    {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation} (scope : RightHeldScope lh lt rh rt heads tails left total active)
    (run : Calling.Prefix callee callers suffix actions world active final after)
    (observed : ∀ slot ∈ pairSharedQuerySlots, LoanEnding.endsBeforeObservation slot suffix = false)
    (querySafe : ∀ slot ∈ pairQuerySlots, actions.all (LocalPreservation.action slot) = true)
    (closedSafe : ∀ slot ∈ [37, 42, 47, 58, 64, 71, 74, 81], actions.all (LocalPreservation.action slot) = true)
    (roots : ∀ slot ∈ [65, 70, 76, 77, 78, 79, 80, 82], ∀ act ∈ actions, keepsRoot slot act) :
    RightHeldScope lh lt rh rt heads tails left total after := by
  refine ⟨prefix_pair_queries_complete run scope.queries observed querySafe,
    scope.matched.through_prefix run (by
      intro slot member
      exact closedSafe slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      (by intro slot member; exact roots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)),
    (run.closed_local_same_calls (index := 71) (by rw [scope.leftWord]; exact ofValue_typed (word_typed _)) (.adt .word)
      (closedSafe _ (by simp))).trans scope.leftWord,
    (run.closed_local_same_calls (index := 74) (by rw [scope.leftHole]; exact headPayloadHole_typed) (.adt .optional)
      (closedSafe _ (by simp))).trans scope.leftHole,
    (run.closed_local_same_calls (index := 81) (by rw [scope.leftWitness]; exact ofValue_typed (result_typed left)) (.adt .embedding)
      (closedSafe _ (by simp))).trans scope.leftWitness,
    (run.closed_local_same_calls (index := 42) (by rw [scope.oldTableEmpty]; exact .empty .u32) .u32
      (closedSafe _ (by simp))).trans scope.oldTableEmpty, ?_⟩
  intro slot member
  rw [run.shape.2.2 slot (roots slot (List.mem_append_right [65, 70] member))]
  exact scope.retired slot member

theorem pair_right_payload_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairLeftScope lh lt rh rt heads tails total (some left) table world active)
    (count : 83 ≤ active.count) (unbound : active.roots 82 = none) :
    ∃ final after,
      Calling.Prefix callee callers (rightCode 6) (rightActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 81 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨binding81, root81, raw81⟩ := scope.payloadRoot
  obtain ⟨final, after, run, machine, rootsAfter, countAfter, frameAfter, hole, witness, dead82, memoryAfter⟩ :=
    original_optional_payload_complete h callee (rightCode 6) 74 82 81 (by decide) (by decide) (by decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> decide) left scope.resultValue scope.payloadEmpty root81 raw81 (by omega) unbound
  have whole : Calling.Prefix callee callers (rightCode 6) (rightActions.take 6) world active final after := run
  have queriesAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete whole scope.queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  have matchedAfter := scope.matched.through_prefix whole
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [rightActions, keepsRoot])
  refine ⟨final, after, whole, machine, ⟨⟨queriesAfter, matchedAfter, ?_, hole, witness, ?_, ?_⟩, ?_⟩,
    rootsAfter, countAfter, frameAfter, memoryAfter⟩
  · exact (whole.closed_local_same_calls (index := 71) (by rw [scope.wordValue]; exact ofValue_typed (word_typed _))
      (.adt .word) (by decide +kernel)).trans scope.wordValue
  · exact (whole.closed_local_same_calls (index := 42) (by rw [scope.oldTableEmpty]; exact .empty .u32)
      .u32 (by decide +kernel)).trans scope.oldTableEmpty
  · intro slot member
    have selected : slot ∈ [76, 77, 78, 79, 80] ∨ slot = 82 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
    rcases selected with old | rfl
    · rw [rootsAfter]; exact scope.retired slot old
    · exact dead82
  · exact (whole.closed_local_same_calls (index := 75) (by rw [scope.tableValue]; exact ofValue_typed (table_typed table))
      (.adt .table) (by decide +kernel)).trans scope.tableValue

end SubtreeProofs.Rust.SourceEval.Evaluator
