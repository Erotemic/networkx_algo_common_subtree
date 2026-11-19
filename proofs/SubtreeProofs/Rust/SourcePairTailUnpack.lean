module

public import SubtreeProofs.Rust.SourcePairTailRetire
public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourcePrefixFrame

/-! Move the actual recursive output fields into tail-result/table locals,
retire the moved-out output tuple and open the tail-payload temporary. Both
success and failure results retain the exact native table for later routing. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_tail_unpack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 43 = Slot.ofValue (encodeOutput result table))
    (count : 48 ≤ active.count) (unbound : ∀ slot ∈ [41, 42, 47], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers tailCases (tailActions.drop 17) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 41 = Slot.ofValue (encodeOption result) ∧ after.state 42 = Slot.ofValue (encodeTable table) ∧
      after.state 47 = .empty ∧
      (∃ binding, after.roots 47 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      after.roots 43 = none ∧
      (∀ slot ∈ [41, 42, 47], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [41, 42, 43, 47] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have firstHoleTyped : SlotTyped (headOptionHole table) (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (ofValue_typed (table_typed table)) .nil))
  have secondHoleTyped : SlotTyped headOutputHole (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (.empty (.adt .table)) .nil))
  obtain ⟨w41, a41, run41, m41, roots41, count41, frame41, hole41, value41, memory41⟩ :=
    original_project_view_complete h callee (tailCode 19) (source := 43) (destination := 41) (place := .field (.local 43) none 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [output]; exact head_option_take result table)
      firstHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (option_typed result) (.adt .optional)
      (by omega) (unbound 41 (by simp))
  obtain ⟨w42, a42, run42, m42, roots42, count42, frame42, hole42, value42, memory42⟩ :=
    original_project_view_complete m41 callee (tailCode 21) (source := 43) (destination := 42) (place := .field (.local 43) none 1)
      (by decide) (by decide) (by decide) rfl trivial (by rw [hole41]; exact head_table_take table)
      secondHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (table_typed table) (.adt .table)
      (by rw [count41]; omega) (by simpa [roots41, Roots.set] using unbound 42 (by simp))
  obtain ⟨root43, bound43⟩ := Activation.root_of_materialize h.native.valid (by rw [output]; exact Slot.materialize_ofValue _)
  have bound43a42 : a42.roots 43 = some root43 := by simpa [roots42, roots41, Roots.set] using bound43
  have plan : RetirementPlan a42.roots [.drop 43, .storageDead 43] (a42.roots.set 43 none) :=
    .drop bound43a42 (.dead bound43a42 (.nil _))
  have zero : ZeroRetirement [.drop 43, .storageDead 43] a42.state := by
    intro slot member
    have same : slot = 43 := by simpa using member
    subst slot
    rw [hole42]
    simp [headOutputHole, Slot.dropWork, dropFields, DropWork.plus]
  obtain ⟨wr, ar, cleanup, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (tailCode 23) m42 rfl zero
  let prepared := ar.forgetRefs (tailCode 23)
  have mp := mr.prepare (tailCode 23)
  let root47 : Binding := ⟨wr.memory.length, wr.memory.length⟩
  let final := wr.allocate (.stack prepared.frame 47 wr.memory.length) (.node .tuple 0 [])
  let after : Activation := {prepared with roots := prepared.roots.set 47 (some root47), state := prepared.state.set 47 .empty}
  obtain ⟨live47, finalMachine⟩ := mp.storageLive (slot := 47) (by change 47 < ar.count; rw [countR, count42, count41]; omega)
    (by simpa [prepared, Activation.forgetRefs, rootsR, roots42, roots41, Roots.set] using unbound 47 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after at finalMachine
  have last3 : Calling.Prefix callee callers tailCases (tailActions.drop 21) w42 a42 final after :=
    Calling.Prefix.append (suffix := tailCases) (rest := [.storageLive 47]) cleanup
      (.cons (Calling.instruction_noncall_run (act := .storageLive 47) live47) (.nil _ _))
  have last5 : Calling.Prefix callee callers tailCases (tailActions.drop 19) w41 a41 final after :=
    Calling.Prefix.append (suffix := tailCases) (rest := tailActions.drop 21) run42 last3
  have whole : Calling.Prefix callee callers tailCases (tailActions.drop 17) world active final after :=
    Calling.Prefix.append (suffix := tailCases) (rest := tailActions.drop 19) run41 last5
  refine ⟨final, after, whole, finalMachine, countR.trans (count42.trans count41), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1
  · exact (last5.closed_local_same (index := 41) m41.native.valid m41.native.callersValid m41.native.wellFormed
      (by rw [value41]; exact ofValue_typed (option_typed result)) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans value41
  · exact (last3.closed_local_same (index := 42) m42.native.valid m42.native.callersValid m42.native.wellFormed
      (by rw [value42]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans value42
  · simp only [after, Partial.Locals.set, ite_true]
  · exact ⟨root47, by simp [after, Roots.set], (wr.allocate_spec _ _).2.1⟩
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [after, prepared, Activation.forgetRefs, rootsR, roots42, roots41, Roots.set]
  · intro slot outside
    have different : slot ≠ 41 ∧ slot ≠ 42 ∧ slot ≠ 43 ∧ slot ≠ 47 := by simpa using outside
    simp only [after, prepared, Activation.forgetRefs, rootsR, roots42, roots41, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · intro index binding root raw read
    have other : index ≠ 41 := by intro same; subst index; rw [unbound 41 (by simp)] at root; cases root
    have rootA41 : a41.roots index = some binding := by simpa only [roots41, Roots.set, other, ite_false] using root
    have memory42 := memory42 index binding rootA41 raw (memory41 index binding root raw read)
    have memoryR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact memory42
    exact (wr.allocate_keeps mr.native.wellFormed _ _ []).memory _ _ memoryR

end SubtreeProofs.Rust.SourceEval.Evaluator
