module

public import SubtreeProofs.Rust.SourcePairSecondChoice

/-! Compose both actual parent choices and all fifteen instructions from
finishCode 6 through finishCode 21, retaining the selected native witness and
both independently bounded owned contraction queries. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def selectedWitness (candidate left right : CommonEmbedding) : CommonEmbedding :=
  OrderedSolver.selectResult (OrderedSolver.selectResult candidate left) right

theorem pair_choices_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (candidate left right : CommonEmbedding)
    (candidateValue : active.state 64 = Slot.ofValue (encodeResult candidate))
    (leftValue : active.state 81 = Slot.ofValue (encodeResult left))
    (rightValue : active.state 95 = Slot.ofValue (encodeResult right))
    (candidateAbove : LocalOwnersAbove before.memory.length world active 64)
    (leftAbove : LocalOwnersAbove before.memory.length world active 81)
    (rightAbove : LocalOwnersAbove before.memory.length world active 95)
    (wordsAbove : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot)
    (count : 104 ≤ active.count) (unbound : ∀ slot ∈ [99, 100, 101, 102, 103], active.roots slot = none) :
    ∃ (firstArgumentWorld : World) (firstArgumentActive : Activation) (firstCallWorld : World) (firstCallActive : Activation) (middle : World) (current : Activation) (secondArgumentWorld : World) (secondArgumentActive : Activation) (secondCallWorld : World) (secondCallActive : Activation) (final : World) (after : Activation),
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 99 = Slot.ofValue (encodeResult (selectedWitness candidate left right)) ∧
      (∀ slot ∈ [64, 81, 95, 100, 101, 102, 103], after.state slot = .empty) ∧
      (∀ slot ∈ [100, 101, 102, 103], after.roots slot = none) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [99, 100, 101, 102, 103] → after.roots slot = active.roots slot) ∧
      LocalOwnersAbove before.memory.length final after 99 ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [64, 81, 95, 99, 100, 101, 102, 103] →
        (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      (∀ slot ∈ [1, 2], after.state slot = active.state slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      ∀ fuel budget, 0 < fuel →
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 6).take 9) world active middle current ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 15).take 6) middle current final after ∧
        Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 6).take 15) world active final after ∧
        Derived.call (Recursive.original budget fuel) firstArgumentWorld (firstArgumentActive.forgetRefs (finishCode 12)) callers
          .chooseLonger [.move (.local 101), .move (.local 102)] 100 =
            some (firstCallWorld, firstCallActive, choiceCallCost 101 102 100 candidate left) ∧
        Derived.call (Recursive.original budget fuel) secondArgumentWorld (secondArgumentActive.forgetRefs (finishCode 17)) callers
          .chooseLonger [.move (.local 100), .move (.local 103)] 99 =
            some (secondCallWorld, secondCallActive, choiceCallCost 100 103 99 (OrderedSolver.selectResult candidate left) right) := by
  obtain ⟨wa1, aa1, wc1, ac1, middle, current, firstMachine, firstSelected, empty64, empty81, empty99, root99,
    retired1, count1, frame1, roots1, fresh1, held1, kept1, queries1, memory1, stable1⟩ :=
    pair_first_choice_complete h candidate left candidateValue leftValue candidateAbove leftAbove
      (by intro slot member
          have selected : slot ∈ [71, 85] ∨ slot = 95 := by simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
          rcases selected with old | rfl
          · exact wordsAbove slot old
          · exact rightAbove)
      (by omega) (by intro slot member; exact unbound slot (List.mem_append_left [103] member))
  have rightAfter : current.state 95 = Slot.ofValue (encodeResult right) :=
    (kept1 95 (by decide) (.adt .embedding) (by rw [rightValue]; exact ofValue_typed (result_typed right)) (.adt .embedding)).trans rightValue
  obtain ⟨wa2, aa2, wc2, ac2, final, after, machine, selected, empty95, empty100, retired2, count2, frame2,
    roots2, fresh2, words2, kept2, queries2, memory2, stable2⟩ :=
    pair_second_choice_complete firstMachine (OrderedSolver.selectResult candidate left) right firstSelected rightAfter fresh1
      (held1 95 (by simp)) (by intro slot member; exact held1 slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto))
      empty99 root99 (by rw [count1]; exact count)
      (by rw [roots1 103 (by decide)]; exact unbound 103 (by simp))
  have stable : ∀ fuel budget, 0 < fuel →
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 15) ((finishActions.drop 6).take 9) world active middle current ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 15).take 6) middle current final after ∧
      Calling.Prefix (Recursive.original budget fuel) callers (finishCode 21) ((finishActions.drop 6).take 15) world active final after ∧
      Derived.call (Recursive.original budget fuel) wa1 (aa1.forgetRefs (finishCode 12)) callers .chooseLonger
        [.move (.local 101), .move (.local 102)] 100 = some (wc1, ac1, choiceCallCost 101 102 100 candidate left) ∧
      Derived.call (Recursive.original budget fuel) wa2 (aa2.forgetRefs (finishCode 17)) callers .chooseLonger
        [.move (.local 100), .move (.local 103)] 99 = some (wc2, ac2, choiceCallCost 100 103 99 (OrderedSolver.selectResult candidate left) right) := by
    intro fuel budget positive
    obtain ⟨_, call1, _, _, first9⟩ := stable1 fuel budget positive
    obtain ⟨_, call2, _, _, last6⟩ := stable2 fuel budget positive
    exact ⟨first9, last6, Calling.Prefix.append (suffix := finishCode 21) (rest := (finishActions.drop 15).take 6) first9 last6, call1, call2⟩
  have whole := (stable 1 0 (by decide)).2.2.1
  have retired : ∀ slot ∈ [100, 101, 102, 103], after.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact retired2 100 (by simp)
    · rw [roots2 101 (by decide)]; exact retired1 101 (by simp)
    · rw [roots2 102 (by decide)]; exact retired1 102 (by simp)
    · exact retired2 103 (by simp)
  refine ⟨wa1, aa1, wc1, ac1, middle, current, wa2, aa2, wc2, ac2, final, after, machine, selected, ?_, retired,
    count2.trans count1, frame2.trans frame1, ?_, fresh2, words2, ?_, ?_, ?_, stable⟩
  · intro slot member
    have split : slot = 64 ∨ slot = 81 ∨ slot = 95 ∨ slot ∈ [100, 101, 102, 103] := by
      simpa only [List.mem_cons, List.not_mem_nil, or_false, or_assoc] using member
    rcases split with rfl | rfl | rfl | old
    · exact (kept2 64 (by decide) .u32 (by rw [empty64]; exact .empty _) .u32).trans empty64
    · exact (kept2 81 (by decide) .u32 (by rw [empty81]; exact .empty _) .u32).trans empty81
    · exact empty95
    · obtain ⟨_, frame⟩ := machine.native.valid.2
      simpa only [retired slot old] using frame.slots slot
  · intro slot outside
    have different : slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 ∧ slot ≠ 103 := by simpa using outside
    rw [roots2 slot (by simp [different.2.1, different.2.2.2.2]), roots1 slot (by simp [different.1, different.2.1, different.2.2.1, different.2.2.2.1])]
  · intro slot outside unshared
    apply whole.unshared_local_same_calls unshared
    have different : slot ≠ 64 ∧ slot ≠ 81 ∧ slot ≠ 95 ∧ slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 ∧ slot ≠ 103 := by simpa using outside
    simp [finishActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operands, LocalPreservation.operand,
      splitPlace, different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2.1, different.2.2.2.2.2.1,
      different.2.2.2.2.2.2.1, different.2.2.2.2.2.2.2]
  · intro slot member
    exact (queries2 slot member).trans (queries1 slot member)
  · intro slot binding root cell read
    have outside : slot ∉ [99, 100, 101, 102, 103] := by intro member; rw [unbound slot member] at root; cases root
    have different : slot ≠ 99 ∧ slot ≠ 100 ∧ slot ≠ 101 ∧ slot ≠ 102 ∧ slot ≠ 103 := by simpa using outside
    have root1 : current.roots slot = some binding := by
      rw [roots1 slot (by simp [different.1, different.2.1, different.2.2.1, different.2.2.2.1])]; exact root
    exact memory2 slot binding different.1 root1 cell (memory1 slot binding root cell read)

end SubtreeProofs.Rust.SourceEval.Evaluator
