module

public import SubtreeProofs.Rust.SourcePairOlderMasks
public import SubtreeProofs.Rust.SourcePairFinishPacking
public import SubtreeProofs.Rust.SourceFreshRetirement

/-! Construct every remaining successful-right cleanup instruction. The owned
query words are dropped with derived freshness; older holes and ended views
carry no owners. Original table/query/caller aliases remain permitted. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def pairCleanupZeroSlots : List Nat :=
  [1, 2, 3, 13, 27, 28, 29, 30, 31, 32, 37, 41, 42, 47, 51, 58, 64, 74, 75, 81, 88, 89, 95]

theorem pair_finish_cleanup_zero {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : FinishPackedScope lh lt rh rt heads tails left right table total active)
    (older : PairOlderMasks active) :
    ∀ slot ∈ pairCleanupZeroSlots, (active.state slot).dropWork.boxes = 0 := by
  intro slot member
  simp only [pairCleanupZeroSlots, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.zero _ (by decide)
    | exact older.subtotalZero
    | (rw [older.tableEmpty]; simp [Slot.dropWork])
    | (rw [older.headTableEmpty]; simp [Slot.dropWork])
    | (rw [older.headHole]; simp [Slot.dropWork, dropFields, DropWork.plus])
    | (rw [older.tailHole]; simp [Slot.dropWork, dropFields, DropWork.plus])
    | (rw [scope.headHole]; simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus])
    | (rw [scope.tailHole]; simp [resultWordHole, Slot.dropWork, dropFields, DropWork.plus])
    | (rw [scope.headTableEmpty]; simp [Slot.dropWork])
    | (rw [scope.leftTableEmpty]; simp [Slot.dropWork])
    | (rw [scope.totalValue]; simp [Slot.dropWork])
    | (rw [scope.leftHole]; simp [headPayloadHole, Slot.dropWork, dropFields, DropWork.plus])
    | (rw [scope.rightHole]; simp [headPayloadHole, Slot.dropWork, dropFields, DropWork.plus])
    | (rw [scope.moved _ (by decide)]; simp [Slot.dropWork])

theorem pair_finish_cleanup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : FinishPackedScope lh lt rh rt heads tails left right table total active)
    (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot)
    (count : 113 ≤ active.count)
    (above : LocalResultOwnersAbove before.memory.length world active 0)
    (held : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot) :
    ∃ final after,
      Calling.Prefix callee callers .ret (finishActions.drop 56) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 0 = Slot.ofValue (encodeOutput
        (some (selectedWitness (matchedWitness heads tails total) left right))
        (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)) ∧
      LocalResultOwnersAbove before.memory.length final after 0 ∧
      (∃ binding, after.roots 0 = some binding) ∧
      (∀ slot, slot ≠ 0 → after.roots slot = none ∧ after.state slot = .empty) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ final.memory = world.memory := by
  have zero := pair_finish_cleanup_zero h scope older
  have ready : retirementReady (rootPresence active.roots) (finishActions.drop 56) = true := by
    rw [present]
    decide +kernel
  have fresh : ∀ slot, Action.drop slot ∈ finishActions.drop 56 ∨ Action.storageDead slot ∈ finishActions.drop 56 →
      LocalOwnersAbove before.memory.length world active slot := by
    intro slot member
    by_cases leftQuery : slot = 71
    · subst slot; exact held 71 (by simp)
    by_cases rightQuery : slot = 85
    · subst slot; exact held 85 (by simp)
    apply LocalOwnersAbove.of_zero (zero slot ?_)
    simp [finishActions] at member
    simp only [pairCleanupZeroSlots, List.mem_cons, List.not_mem_nil, or_false]
    omega
  have checks : retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) (finishActions.drop 56) := by
    simp only [finishActions, List.drop_succ_cons, List.drop_zero, retirementZeroChecks, clearBoxCount]
    simp only [Nat.reduceEqDiff, ite_true, ite_false]
    repeat' constructor
    all_goals exact zero _ (by decide +kernel)
  obtain ⟨final, after, steps, machine, roots, countAfter, memory⟩ :=
    (RetirementPlan.of_presence ready).complete_fresh callee .ret h rfl
      (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega) fresh checks
  have root0 : after.roots 0 = active.roots 0 := steps.shape.2.2 0 (by decide +kernel)
  have output := (steps.closed_local_same_calls
    (by rw [scope.output]; exact ofValue_typed (encodeOutput_typed _ _))
    (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (by decide +kernel)).trans scope.output
  have finalPresence : rootPresence after.roots = fun slot => [0].contains slot := by
    rw [steps.root_presence, present, rootPresence_fold_contains]
    have same : ((finishActions.drop 56).foldl rootSlotsStep pairRightLiveRoots).Perm [0] := by decide +kernel
    funext slot
    exact Bool.eq_iff_iff.mpr (by simpa only [List.contains_iff_mem] using same.mem_iff)
  refine ⟨final, after, steps, machine, output, above.memory_same memory root0,
    rootPresence.bound finalPresence (by decide), ?_, countAfter, steps.shape.1, memory⟩
  intro slot nonzero
  have unbound : after.roots slot = none := by
    have absent : (after.roots slot).isSome = false := by
      change rootPresence after.roots slot = false
      rw [finalPresence]
      simp [nonzero]
    cases root : after.roots slot with
    | none => rfl
    | some binding => simp [root] at absent
  exact ⟨unbound, by obtain ⟨_, frame⟩ := machine.native.valid.2; simpa only [unbound] using frame.slots slot⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
