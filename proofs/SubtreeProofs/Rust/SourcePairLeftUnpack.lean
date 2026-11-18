module

public import SubtreeProofs.Rust.SourcePairLeftArgumentsRetire
public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourcePrefixFrame
public import SubtreeProofs.Rust.SourceFreshWritePrefixes

/-! Move the actual recursive output fields into left-result/table locals,
retire the moved-out output tuple and the ended word-view root, then open payload 81. Both
success and failure results retain the exact native table for later routing. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_unpack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 76 = Slot.ofValue (encodeOutput result table))
    (empty78 : active.state 78 = .empty) (root78 : ∃ binding, active.roots 78 = some binding)
    (count : 82 ≤ active.count) (unbound : ∀ slot ∈ [74, 75, 81], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers matchedCases ((matchedActions.drop 52).take 8) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 74 = Slot.ofValue (encodeOption result) ∧ after.state 75 = Slot.ofValue (encodeTable table) ∧
      after.state 81 = .empty ∧
      (∃ binding, after.roots 81 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      after.roots 76 = none ∧ after.roots 78 = none ∧
      (∀ slot ∈ [74, 75, 81], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [74, 75, 76, 78, 81] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      Heap.Extends world.memory final.memory := by
  have firstHoleTyped : SlotTyped (headOptionHole table) (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (ofValue_typed (table_typed table)) .nil))
  have secondHoleTyped : SlotTyped headOutputHole (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (.empty (.adt .table)) .nil))
  obtain ⟨w74, a74, run74, m74, roots74, count74, frame74, hole74, value74, memory74⟩ :=
    original_project_view_complete h callee (matchedCode 54) (source := 76) (destination := 74) (place := .field (.local 76) none 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [output]; exact head_option_take result table)
      firstHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (option_typed result) (.adt .optional)
      (by omega) (unbound 74 (by simp))
  obtain ⟨w75, a75, run75, m75, roots75, count75, frame75, hole75, value75, memory75⟩ :=
    original_project_view_complete m74 callee (matchedCode 56) (source := 76) (destination := 75) (place := .field (.local 76) none 1)
      (by decide) (by decide) (by decide) rfl trivial (by rw [hole74]; exact head_table_take table)
      secondHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (table_typed table) (.adt .table)
      (by rw [count74]; omega) (by simpa [roots74, Roots.set] using unbound 75 (by simp))
  obtain ⟨root76, bound76⟩ := Activation.root_of_materialize h.native.valid (by rw [output]; exact Slot.materialize_ofValue _)
  have bound76a75 : a75.roots 76 = some root76 := by simpa [roots75, roots74, Roots.set] using bound76
  obtain ⟨binding78, bound78⟩ := root78
  have bound78a75 : a75.roots 78 = some binding78 := by simpa [roots75, roots74, Roots.set] using bound78
  have first4 : Calling.Prefix callee callers (matchedCode 56) ((matchedActions.drop 52).take 4) world active w75 a75 :=
    Calling.Prefix.append (suffix := matchedCode 56) (rest := (matchedActions.drop 54).take 2) run74 run75
  have empty78a75 : a75.state 78 = .empty :=
    (first4.unshared_local_same_calls (index := 78) (by rw [empty78]; simp) (by decide +kernel)).trans empty78
  have plan : RetirementPlan a75.roots [.drop 76, .storageDead 78, .storageDead 76] ((a75.roots.set 78 none).set 76 none) :=
    .drop bound76a75 (.dead bound78a75 (.dead (binding := root76)
      (by simpa [Roots.set] using bound76a75) (.nil _)))
  have zero : ZeroRetirement [.drop 76, .storageDead 78, .storageDead 76] a75.state := by
    intro slot member
    have selected : slot = 76 ∨ slot = 78 := by
      simp at member
      tauto
    rcases selected with rfl | rfl
    · rw [hole75]; simp [headOutputHole, Slot.dropWork, dropFields, DropWork.plus]
    · rw [empty78a75]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, cleanup, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (matchedCode 59) m75 rfl zero
  let prepared := ar.forgetRefs (matchedCode 59)
  have mp := mr.prepare (matchedCode 59)
  let root81 : Binding := ⟨wr.memory.length, wr.memory.length⟩
  let final := wr.allocate (.stack prepared.frame 81 wr.memory.length) (.node .tuple 0 [])
  let after : Activation := {prepared with roots := prepared.roots.set 81 (some root81), state := prepared.state.set 81 .empty}
  obtain ⟨live81, finalMachine⟩ := mp.storageLive (slot := 81) (by change 81 < ar.count; rw [countR, count75, count74]; omega)
    (by simpa [prepared, Activation.forgetRefs, rootsR, roots75, roots74, Roots.set] using unbound 81 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after at finalMachine
  have last4 : Calling.Prefix callee callers matchedCases ((matchedActions.drop 56).take 4) w75 a75 final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := [.storageLive 81]) cleanup
      (.cons (Calling.instruction_noncall_run (act := .storageLive 81) live81) (.nil _ _))
  have last6 : Calling.Prefix callee callers matchedCases ((matchedActions.drop 54).take 6) w74 a74 final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 56).take 4) run75 last4
  have whole : Calling.Prefix callee callers matchedCases ((matchedActions.drop 52).take 8) world active final after :=
    Calling.Prefix.append (suffix := matchedCases) (rest := (matchedActions.drop 54).take 6) run74 last6
  refine ⟨final, after, whole, finalMachine, countR.trans (count75.trans count74), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1
  · exact (last6.closed_local_same_calls (index := 74) (by rw [value74]; exact ofValue_typed (option_typed result)) (.adt .optional) (by decide +kernel)).trans value74
  · exact (last4.closed_local_same_calls (index := 75) (by rw [value75]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel)).trans value75
  · simp only [after, Partial.Locals.set, ite_true]
  · exact ⟨root81, by simp [after, Roots.set], (wr.allocate_spec _ _).2.1⟩
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [after, prepared, Activation.forgetRefs, rootsR, roots75, roots74, Roots.set]
  · intro slot outside
    have different : slot ≠ 74 ∧ slot ≠ 75 ∧ slot ≠ 76 ∧ slot ≠ 78 ∧ slot ≠ 81 := by simpa using outside
    simp only [after, prepared, Activation.forgetRefs, rootsR, roots75, roots74, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2.1, different.2.2.2.2, ite_false]
  · intro index binding root raw read
    have other : index ≠ 74 := by intro same; subst index; rw [unbound 74 (by simp)] at root; cases root
    have rootA74 : a74.roots index = some binding := by simpa only [roots74, Roots.set, other, ite_false] using root
    have memory75 := memory75 index binding rootA74 raw (memory74 index binding root raw read)
    have memoryR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact memory75
    exact (wr.allocate_keeps mr.native.wellFormed _ _ []).memory _ _ memoryR
  · have first := run74.open_assign_memory
    have second := run75.open_assign_memory
    have extendsR : Heap.Extends w75.memory wr.memory := by rw [memoryR]; exact Heap.Extends.refl _
    exact (first.trans second).trans (extendsR.trans (Heap.Extends.append _ _))

end SubtreeProofs.Rust.SourceEval.Evaluator
