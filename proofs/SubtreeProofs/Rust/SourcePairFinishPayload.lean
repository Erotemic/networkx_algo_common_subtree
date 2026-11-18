module

public import SubtreeProofs.Rust.SourcePairRightFreshEntry
public import SubtreeProofs.Rust.SourcePairFinishProgram

/-! Construct the first six actual successful-right instructions. The new scope
records ended child views rather than preserving stale masks. The derived right
witness owner bound survives extraction into held payload 95. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem optional_payload_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {bound source temporary destination : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (sourceTemp : source ≠ temporary) (tempDestination : temporary ≠ destination)
    (above : LocalOwnersAbove bound world active source)
    (steps : Calling.Prefix callee callers suffix (optionalPayloadActions source temporary destination) world active final after) :
    LocalOwnersAbove bound final after destination := by
  have plan : OwnerTransfer source (optionalPayloadActions source temporary destination) destination := by
    refine .keep rfl ?_ (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl)
      (.assign (fun _ _ _ h => OperandSourcesAbove.single_move h rfl) (.keep rfl ?_ (.keep rfl ?_ (.keep rfl rfl (.nil destination))))))
    · exact decide_eq_true sourceTemp
    · exact decide_eq_true (Ne.symm tempDestination)
    · exact decide_eq_true (Ne.symm tempDestination)
  exact steps.owner_transfer plan ha hc hw above

structure FinishPayloadScope (lh lt rh rt : BalancedWord) (heads tails left right : CommonEmbedding)
    (table : MemoTable) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  leftQuery : active.state 1 = .shared (encodeWord (.Pair lh lt))
  rightQuery : active.state 2 = .shared (encodeWord (.Pair rh rt))
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  endedViews : ∀ slot ∈ [27, 28, 29, 30], active.state slot = .empty
  matched : MatchedCandidateScope heads tails total active
  leftWord : active.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt))
  leftHole : active.state 74 = headPayloadHole
  leftWitness : active.state 81 = Slot.ofValue (encodeResult left)
  rightWord : active.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt))
  rightHole : active.state 88 = headPayloadHole
  rightWitness : active.state 95 = Slot.ofValue (encodeResult right)
  tableValue : active.state 89 = Slot.ofValue (encodeTable table)
  headTableEmpty : active.state 42 = .empty
  leftTableEmpty : active.state 75 = .empty
  retired : ∀ slot ∈ [86, 87, 90, 91, 92, 93, 94, 96], active.roots slot = none

theorem pair_finish_payload_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding}
    {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (count : 97 ≤ active.count) (unbound : active.roots 96 = none) :
    ∃ final after,
      Calling.Prefix callee callers (finishCode 6) (finishActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      FinishPayloadScope lh lt rh rt heads tails left right table total after ∧
      LocalOwnersAbove before.memory.length final after 95 ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 95 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨binding, root, raw⟩ := scope.payloadRoot
  obtain ⟨final, after, run, machine, rootsAfter, countAfter, frameAfter, hole, witness, dead96, memoryAfter⟩ :=
    original_optional_payload_complete h callee (finishCode 6) 88 96 95 (by decide) (by decide) (by decide)
      (by intro slot member
          simp only [List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl <;> decide) right scope.resultValue scope.payloadEmpty root raw (by omega) unbound
  have whole : Calling.Prefix callee callers (finishCode 6) (finishActions.take 6) world active final after := run
  have fresh := optional_payload_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by decide) (by decide) above run
  have leftQuery := (whole.retained_local_same_calls (index := 1) (by decide +kernel) (by decide +kernel)).trans scope.held.queries.left
  have rightQuery := (whole.retained_local_same_calls (index := 2) (by decide +kernel) (by decide +kernel)).trans scope.held.queries.right
  have tuple := (whole.unshared_local_same_calls (index := 13)
    (by rw [scope.held.queries.tuple]; intro value impossible; cases impossible) (by decide +kernel)).trans scope.held.queries.tuple
  have matched := scope.held.matched.through_prefix whole
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide +kernel)
    (by intro slot member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [finishActions, List.take, keepsRoot])
  refine ⟨final, after, whole, machine, ⟨leftQuery, rightQuery, tuple, ?_, matched, ?_, ?_, ?_, ?_, hole, witness, ?_, ?_, ?_, ?_⟩,
    fresh, rootsAfter, countAfter, frameAfter, memoryAfter⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact whole.ended_shared_local_empty_calls (by omega) scope.held.queries.leftHead (by decide +kernel) (by decide +kernel)
    · exact whole.ended_shared_local_empty_calls (by omega) scope.held.queries.leftTail (by decide +kernel) (by decide +kernel)
    · exact whole.ended_shared_local_empty_calls (by omega) scope.held.queries.rightHead (by decide +kernel) (by decide +kernel)
    · exact whole.ended_shared_local_empty_calls (by omega) scope.held.queries.rightTail (by decide +kernel) (by decide +kernel)
  · exact (whole.closed_local_same_calls (index := 71) (by rw [scope.held.leftWord]; exact ofValue_typed (word_typed _))
      (.adt .word) (by decide +kernel)).trans scope.held.leftWord
  · exact (whole.closed_local_same_calls (index := 74) (by rw [scope.held.leftHole]; exact headPayloadHole_typed)
      (.adt .optional) (by decide +kernel)).trans scope.held.leftHole
  · exact (whole.closed_local_same_calls (index := 81) (by rw [scope.held.leftWitness]; exact ofValue_typed (result_typed left))
      (.adt .embedding) (by decide +kernel)).trans scope.held.leftWitness
  · exact (whole.closed_local_same_calls (index := 85) (by rw [scope.wordValue]; exact ofValue_typed (word_typed _))
      (.adt .word) (by decide +kernel)).trans scope.wordValue
  · exact (whole.closed_local_same_calls (index := 89) (by rw [scope.tableValue]; exact ofValue_typed (table_typed table))
      (.adt .table) (by decide +kernel)).trans scope.tableValue
  · exact (whole.closed_local_same_calls (index := 42) (by rw [scope.held.oldTableEmpty]; exact .empty .u32)
      .u32 (by decide +kernel)).trans scope.held.oldTableEmpty
  · exact (whole.closed_local_same_calls (index := 75) (by rw [scope.oldTableEmpty]; exact .empty .u32)
      .u32 (by decide +kernel)).trans scope.oldTableEmpty
  · intro slot member
    have selected : slot ∈ [86, 87, 90, 91, 92, 93, 94] ∨ slot = 96 := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
    rcases selected with old | rfl
    · rw [rootsAfter]; exact scope.retired slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at old ⊢; tauto)
    · exact dead96

end SubtreeProofs.Rust.SourceEval.Evaluator
