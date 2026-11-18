module

public import SubtreeProofs.Rust.SourcePairRightPayload
public import SubtreeProofs.Rust.SourceOriginalConcatenate

/-! Construct actual right-concatenation storage and original child-word views
while retaining the owned left witness, matched candidate and original queries. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RightConcatArgumentScope (left right : BalancedWord) (world : World) (active : Activation) : Prop where
  leftValue : active.state 86 = .shared (encodeWord left)
  rightValue : active.state 87 = .shared (encodeWord right)
  resultEmpty : active.state 85 = .empty
  resultRoot : ∃ binding, active.roots 85 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  bound : ∀ slot ∈ [85, 86, 87], ∃ binding, active.roots slot = some binding

theorem pair_right_concat_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : RightPayloadScope lh lt rh rt heads tails left table total active)
    (count : 88 ≤ active.count) (unbound : ∀ slot ∈ [85, 86, 87], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (rightCode 11) ((rightActions.drop 6).take 5) world active final after ∧
      OriginalLoanMachine before callers previous external [87, 86, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightConcatArgumentScope rh rt final after ∧ RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [85, 86, 87] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w85, a85, run85, m85, roots85, count85, frame85, empty85, raw85, memory85⟩ :=
    original_open_local_complete h callee (rightCode 7) (slot := 85) (by decide) (by omega) (unbound 85 (by simp))
  have head85 : a85.state 29 = .shared (.boxed (encodeWord rh)) :=
    (run85.retained_local_same_calls (index := 29) (by decide +kernel) (by decide +kernel)).trans scope.held.queries.rightHead
  obtain ⟨w86, a86, run86, m86, roots86, count86, frame86, value86, memory86⟩ :=
    original_borrow_view_complete m85 callee (rightCode 9) (slot := 29) (destination := 86)
      (place := .deref (.deref (.local 29))) (by simp) (by decide) rfl
      (by rw [head85]; exact .shared _ _) (boxed_word_reborrow_source head85) (NativeData.word rh)
      (by rw [count85]; omega) (by simpa [roots85, Roots.set] using unbound 86 (by simp))
  have first3 : Calling.Prefix callee callers (rightCode 9) ((rightActions.drop 6).take 3) world active w86 a86 :=
    Calling.Prefix.append (suffix := rightCode 9) (rest := (rightActions.drop 7).take 2) run85 run86
  have tail86 : a86.state 30 = .shared (.boxed (encodeWord rt)) :=
    (first3.retained_local_same_calls (index := 30) (by decide +kernel) (by decide +kernel)).trans scope.held.queries.rightTail
  obtain ⟨final, after, run87, machine, roots87, count87, frame87, value87, memory87⟩ :=
    original_borrow_view_complete m86 callee (rightCode 11) (slot := 30) (destination := 87)
      (place := .deref (.deref (.local 30))) (by simp) (by decide) rfl
      (by rw [tail86]; exact .shared _ _) (boxed_word_reborrow_source tail86) (NativeData.word rt)
      (by rw [count86, count85]; omega) (by simpa [roots86, roots85, Roots.set] using unbound 87 (by simp))
  have whole : Calling.Prefix callee callers (rightCode 11) ((rightActions.drop 6).take 5) world active final after :=
    Calling.Prefix.append (suffix := rightCode 11) (rest := (rightActions.drop 9).take 2) first3 run87
  have heldAfter := scope.held.through_prefix whole
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
  let root85 : Binding := ⟨world.memory.length, world.memory.length⟩
  have bound85a85 : a85.roots 85 = some root85 := by simp [roots85, root85, Roots.set]
  have bound85a86 : a86.roots 85 = some root85 := by simpa [roots86, Roots.set] using bound85a85
  have last4 : Calling.Prefix callee callers (rightCode 11) ((rightActions.drop 7).take 4) w85 a85 final after :=
    Calling.Prefix.append (suffix := rightCode 11) (rest := (rightActions.drop 9).take 2) run86 run87
  refine ⟨final, after, whole, machine, ?_, ⟨heldAfter, ?_⟩,
    count87.trans (count86.trans count85), frame87.trans (frame86.trans frame85), ?_, ?_⟩
  · refine ⟨(run87.retained_local_same_calls (index := 86) (by decide +kernel) (by decide +kernel)).trans value86, value87,
      (last4.closed_local_same_calls (index := 85) (by rw [empty85]; exact .empty .u32) .u32 (by decide +kernel)).trans empty85,
      ⟨root85, by simpa [roots87, Roots.set] using bound85a86,
        memory87 85 root85 bound85a86 _ (memory86 85 root85 bound85a85 _ raw85)⟩, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [roots87, roots86, roots85, Roots.set]
  · exact (whole.closed_local_same_calls (index := 75) (by rw [scope.tableValue]; exact ofValue_typed (table_typed table))
      (.adt .table) (by decide +kernel)).trans scope.tableValue
  · intro slot outside
    have different : slot ≠ 85 ∧ slot ≠ 86 ∧ slot ≠ 87 := by simpa using outside
    simp only [roots87, roots86, roots85, Roots.set, different.1, different.2.1, different.2.2, ite_false]
  · intro index binding root raw memoryRead
    have not85 : index ≠ 85 := by intro same; subst index; rw [unbound 85 (by simp)] at root; cases root
    have not86 : index ≠ 86 := by intro same; subst index; rw [unbound 86 (by simp)] at root; cases root
    have rootA85 : a85.roots index = some binding := by simpa only [roots85, Roots.set, not85, ite_false] using root
    have rootA86 : a86.roots index = some binding := by simpa only [roots86, Roots.set, not86, ite_false] using rootA85
    exact memory87 index binding rootA86 raw (memory86 index binding rootA85 raw (memory85 index binding root raw memoryRead))

end SubtreeProofs.Rust.SourceEval.Evaluator
