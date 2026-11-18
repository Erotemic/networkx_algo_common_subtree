module

public import SubtreeProofs.Rust.SourcePairRightArgumentsRetire
public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourcePrefixFrame
public import SubtreeProofs.Rust.SourceFreshWritePrefixes

/-! Move the actual recursive output fields into right-result/table locals,
retire the moved-out output tuple and the ended word-view root, then open payload 95. Both
success and failure results retain the exact native table for later routing. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_unpack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 90 = Slot.ofValue (encodeOutput result table))
    (empty93 : active.state 93 = .empty) (root93 : ∃ binding, active.roots 93 = some binding)
    (count : 96 ≤ active.count) (unbound : ∀ slot ∈ [88, 89, 95], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers rightContractionCases ((rightActions.drop 28).take 8) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 88 = Slot.ofValue (encodeOption result) ∧ after.state 89 = Slot.ofValue (encodeTable table) ∧
      after.state 95 = .empty ∧
      (∃ binding, after.roots 95 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      after.roots 90 = none ∧ after.roots 93 = none ∧
      (∀ slot ∈ [88, 89, 95], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [88, 89, 90, 93, 95] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Heap.Extends world.memory final.memory := by
  have firstHoleTyped : SlotTyped (headOptionHole table) (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (ofValue_typed (table_typed table)) .nil))
  have secondHoleTyped : SlotTyped headOutputHole (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (.empty (.adt .table)) .nil))
  obtain ⟨w88, a88, run88, m88, roots88, count88, frame88, hole88, value88, memory88⟩ :=
    original_project_view_complete h callee (rightCode 30) (source := 90) (destination := 88) (place := .field (.local 90) none 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [output]; exact head_option_take result table)
      firstHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (option_typed result) (.adt .optional)
      (by omega) (unbound 88 (by simp))
  obtain ⟨w89, a89, run89, m89, roots89, count89, frame89, hole89, value89, memory89⟩ :=
    original_project_view_complete m88 callee (rightCode 32) (source := 90) (destination := 89) (place := .field (.local 90) none 1)
      (by decide) (by decide) (by decide) rfl trivial (by rw [hole88]; exact head_table_take table)
      secondHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (table_typed table) (.adt .table)
      (by rw [count88]; omega) (by simpa [roots88, Roots.set] using unbound 89 (by simp))
  obtain ⟨root90, bound90⟩ := Activation.root_of_materialize h.native.valid (by rw [output]; exact Slot.materialize_ofValue _)
  have bound90a89 : a89.roots 90 = some root90 := by simpa [roots89, roots88, Roots.set] using bound90
  obtain ⟨binding93, bound93⟩ := root93
  have bound93a89 : a89.roots 93 = some binding93 := by simpa [roots89, roots88, Roots.set] using bound93
  have first4 : Calling.Prefix callee callers (rightCode 32) ((rightActions.drop 28).take 4) world active w89 a89 :=
    Calling.Prefix.append (suffix := rightCode 32) (rest := (rightActions.drop 30).take 2) run88 run89
  have empty93a89 : a89.state 93 = .empty :=
    (first4.unshared_local_same_calls (index := 93) (by rw [empty93]; simp) (by decide +kernel)).trans empty93
  have plan : RetirementPlan a89.roots [.drop 90, .storageDead 93, .storageDead 90] ((a89.roots.set 93 none).set 90 none) :=
    .drop bound90a89 (.dead bound93a89 (.dead (binding := root90)
      (by simpa [Roots.set] using bound90a89) (.nil _)))
  have zero : ZeroRetirement [.drop 90, .storageDead 93, .storageDead 90] a89.state := by
    intro slot member
    have selected : slot = 90 ∨ slot = 93 := by
      simp at member
      tauto
    rcases selected with rfl | rfl
    · rw [hole89]; simp [headOutputHole, Slot.dropWork, dropFields, DropWork.plus]
    · rw [empty93a89]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, cleanup, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (rightCode 35) m89 rfl zero
  let prepared := ar.forgetRefs (rightCode 35)
  have mp := mr.prepare (rightCode 35)
  let root95 : Binding := ⟨wr.memory.length, wr.memory.length⟩
  let final := wr.allocate (.stack prepared.frame 95 wr.memory.length) (.node .tuple 0 [])
  let after : Activation := {prepared with roots := prepared.roots.set 95 (some root95), state := prepared.state.set 95 .empty}
  obtain ⟨live95, finalMachine⟩ := mp.storageLive (slot := 95) (by change 95 < ar.count; rw [countR, count89, count88]; omega)
    (by simpa [prepared, Activation.forgetRefs, rootsR, roots89, roots88, Roots.set] using unbound 95 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after at finalMachine
  have last4 : Calling.Prefix callee callers rightContractionCases ((rightActions.drop 32).take 4) w89 a89 final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := [.storageLive 95]) cleanup
      (.cons (Calling.instruction_noncall_run (act := .storageLive 95) live95) (.nil _ _))
  have last6 : Calling.Prefix callee callers rightContractionCases ((rightActions.drop 30).take 6) w88 a88 final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 32).take 4) run89 last4
  have whole : Calling.Prefix callee callers rightContractionCases ((rightActions.drop 28).take 8) world active final after :=
    Calling.Prefix.append (suffix := rightContractionCases) (rest := (rightActions.drop 30).take 6) run88 last6
  refine ⟨final, after, whole, finalMachine, countR.trans (count89.trans count88), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1
  · exact (last6.closed_local_same_calls (index := 88) (by rw [value88]; exact ofValue_typed (option_typed result)) (.adt .optional) (by decide +kernel)).trans value88
  · exact (last4.closed_local_same_calls (index := 89) (by rw [value89]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel)).trans value89
  · simp only [after, Partial.Locals.set, ite_true]
  · exact ⟨root95, by simp [after, Roots.set], (wr.allocate_spec _ _).2.1⟩
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [after, prepared, Activation.forgetRefs, rootsR, roots89, roots88, Roots.set]
  · intro slot outside
    have different : slot ≠ 88 ∧ slot ≠ 89 ∧ slot ≠ 90 ∧ slot ≠ 93 ∧ slot ≠ 95 := by simpa using outside
    simp only [after, prepared, Activation.forgetRefs, rootsR, roots89, roots88, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2, ite_false]
  · intro index binding root raw read
    have other : index ≠ 88 := by intro same; subst index; rw [unbound 88 (by simp)] at root; cases root
    have rootA88 : a88.roots index = some binding := by simpa only [roots88, Roots.set, other, ite_false] using root
    have memory89 := memory89 index binding rootA88 raw (memory88 index binding root raw read)
    have memoryR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact memory89
    exact (wr.allocate_keeps mr.native.wellFormed _ _ []).memory _ _ memoryR
  · have first := run88.open_assign_memory
    have second := run89.open_assign_memory
    have extendsR : Heap.Extends w89.memory wr.memory := by rw [memoryR]; exact Heap.Extends.refl _
    exact (first.trans second).trans (extendsR.trans (Heap.Extends.append _ _))

end SubtreeProofs.Rust.SourceEval.Evaluator
