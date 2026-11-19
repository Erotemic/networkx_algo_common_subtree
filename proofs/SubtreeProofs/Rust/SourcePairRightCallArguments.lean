module

public import SubtreeProofs.Rust.SourcePairRightWordViews
public import SubtreeProofs.Rust.SourceAnchoredPrefixes

/-! Move the native table into the actual right recursive-call argument while
retaining both original and freshly word-supported query views. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RightContractionArgumentScope (left right : BalancedWord) (table : MemoTable) (world : World) (active : Activation) : Prop where
  left : active.state 91 = .shared (encodeWord left)
  right : active.state 92 = .shared (encodeWord right)
  tableValue : active.state 94 = Slot.ofValue (encodeTable table)
  tableMoved : active.state 75 = .empty
  resultEmpty : active.state 90 = .empty
  result : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  bound : ∀ slot ∈ [90, 91, 92, 94], ∃ binding, active.roots slot = some binding

theorem pair_right_call_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat} {anchor : Resources}
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (h : AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
      [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor world active)
    (callee : Derived.Callees) (payload : RightPayloadScope lh lt rh rt heads tails left table total active)
    (leftView : active.state 91 = .shared (encodeWord (.Pair lh lt)))
    (rightView : active.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)))
    (empty90 : active.state 90 = .empty)
    (root90 : ∃ binding, active.roots 90 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 []))
    (count : 95 ≤ active.count) (unbound : active.roots 94 = none) :
    ∃ final after,
      Calling.Prefix callee callers (rightCode 24) ((rightActions.drop 22).take 2) world active final after ∧
      AnchoredLoanMachine before callers previous external [91, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13]
        [92, 93] 85 (OrderedSolver.appendWord rh rt) anchor final after ∧
      RightContractionArgumentScope (.Pair lh lt) (OrderedSolver.appendWord rh rt) table final after ∧
      RightHeldScope lh lt rh rt heads tails left total after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ≠ 94 → after.roots slot = active.roots slot) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨final, after, whole, machine, roots, countAfter, frameAfter, moved75, tableAfter, memory⟩ :=
    anchored_move_view_complete h callee (rightCode 24) (source := 75) (destination := 94)
      (by decide) (by decide) (by decide) (by decide) payload.tableValue (table_typed table) (.adt .table)
      (by omega) unbound
  have heldAfter := payload.held.through_prefix whole
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
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [keepsRoot])
  have leftAfter : after.state 91 = .shared (encodeWord (.Pair lh lt)) :=
    (whole.retained_local_same_calls (index := 91) (by decide +kernel) (by decide +kernel)).trans leftView
  have rightAfter : after.state 92 = .shared (encodeWord (OrderedSolver.appendWord rh rt)) :=
    (whole.retained_local_same_calls (index := 92) (by decide +kernel) (by decide +kernel)).trans rightView
  obtain ⟨binding90, bound90, raw90⟩ := root90
  refine ⟨final, after, whole, machine, ⟨leftAfter, rightAfter, tableAfter, moved75,
    (whole.closed_local_same_calls (index := 90) (by rw [empty90]; exact .empty .u32) .u32 (by decide +kernel)).trans empty90,
    ⟨binding90, by simpa [roots, Roots.set] using bound90, memory 90 binding90 bound90 _ raw90⟩, ?_⟩,
    heldAfter, countAfter, frameAfter, ?_, memory⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact ⟨binding90, by simpa [roots, Roots.set] using bound90⟩
    · exact Activation.root_of_materialize machine.native.valid (value := .reference (encodeWord (.Pair lh lt)))
        (by rw [leftAfter]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize machine.native.valid (value := .reference (encodeWord (OrderedSolver.appendWord rh rt)))
        (by rw [rightAfter]; simp only [Slot.materialize])
    · exact Activation.root_of_materialize machine.native.valid (by rw [tableAfter]; exact Slot.materialize_ofValue _)
  · intro slot different
    simp only [roots, Roots.set, different, ite_false]

end SubtreeProofs.Rust.SourceEval.Evaluator
