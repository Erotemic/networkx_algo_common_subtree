module

public import SubtreeProofs.Rust.SourcePairHeadRetire
public import SubtreeProofs.Rust.SourceOriginalProjectView
public import SubtreeProofs.Rust.SourcePrefixFrame

/-! Move the actual recursive output fields into head-result/table locals,
retire the moved-out output tuple and open the head-payload temporary. Both
success and failure results retain the exact native table for later routing. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def headOptionHole (table : MemoTable) : Slot := .node .tuple 0 [.empty, Slot.ofValue (encodeTable table)]
def headOutputHole : Slot := .node .tuple 0 [.empty, .empty]

theorem head_option_take (result : Option CommonEmbedding) (table : MemoTable) :
    (Slot.ofValue (encodeOutput result table)).take [.field none 0] = some (encodeOption result, headOptionHole table) := by
  simp [encodeOutput, Slot.ofValue, ofFields, Slot.take, Slot.materialize_ofValue, headOptionHole]

theorem head_table_take (table : MemoTable) :
    (headOptionHole table).take [.field none 1] = some (encodeTable table, headOutputHole) := by
  simp [headOptionHole, headOutputHole, Slot.take, Slot.materialize_ofValue]

theorem pair_head_unpack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {result : Option CommonEmbedding} {table : MemoTable} (output : active.state 33 = Slot.ofValue (encodeOutput result table))
    (count : 38 ≤ active.count) (unbound : ∀ slot ∈ [31, 32, 37], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers headCases (headActions.drop 19) world active final after ∧
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state 31 = Slot.ofValue (encodeOption result) ∧ after.state 32 = Slot.ofValue (encodeTable table) ∧
      after.state 37 = .empty ∧
      (∃ binding, after.roots 37 = some binding ∧ final.memory[binding.address]? = some (.node .tuple 0 [])) ∧
      after.roots 33 = none ∧
      (∀ slot ∈ [31, 32, 37], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [31, 32, 33, 37] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have firstHoleTyped : SlotTyped (headOptionHole table) (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (ofValue_typed (table_typed table)) .nil))
  have secondHoleTyped : SlotTyped headOutputHole (.tuple [.adt .optional, .adt .table]) :=
    .node (.tuple _) (.cons (.empty (.adt .optional)) (.cons (.empty (.adt .table)) .nil))
  obtain ⟨w31, a31, run31, m31, roots31, count31, frame31, hole31, value31, memory31⟩ :=
    original_project_view_complete h callee (headCode 21) (source := 33) (destination := 31) (place := .field (.local 33) none 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [output]; exact head_option_take result table)
      firstHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (option_typed result) (.adt .optional)
      (by omega) (unbound 31 (by simp))
  obtain ⟨w32, a32, run32, m32, roots32, count32, frame32, hole32, value32, memory32⟩ :=
    original_project_view_complete m31 callee (headCode 23) (source := 33) (destination := 32) (place := .field (.local 33) none 1)
      (by decide) (by decide) (by decide) rfl trivial (by rw [hole31]; exact head_table_take table)
      secondHoleTyped (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) (table_typed table) (.adt .table)
      (by rw [count31]; omega) (by simpa [roots31, Roots.set] using unbound 32 (by simp))
  obtain ⟨root33, bound33⟩ := Activation.root_of_materialize h.native.valid (by rw [output]; exact Slot.materialize_ofValue _)
  have bound33a32 : a32.roots 33 = some root33 := by simpa [roots32, roots31, Roots.set] using bound33
  have plan : RetirementPlan a32.roots [.drop 33, .storageDead 33] (a32.roots.set 33 none) :=
    .drop bound33a32 (.dead bound33a32 (.nil _))
  have zero : ZeroRetirement [.drop 33, .storageDead 33] a32.state := by
    intro slot member
    have same : slot = 33 := by simpa using member
    subst slot
    rw [hole32]
    simp [headOutputHole, Slot.dropWork, dropFields, DropWork.plus]
  obtain ⟨wr, ar, cleanup, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (headCode 25) m32 rfl zero
  let prepared := ar.forgetRefs (headCode 25)
  have mp := mr.prepare (headCode 25)
  let root37 : Binding := ⟨wr.memory.length, wr.memory.length⟩
  let final := wr.allocate (.stack prepared.frame 37 wr.memory.length) (.node .tuple 0 [])
  let after : Activation := {prepared with roots := prepared.roots.set 37 (some root37), state := prepared.state.set 37 .empty}
  obtain ⟨live37, finalMachine⟩ := mp.storageLive (slot := 37) (by change 37 < ar.count; rw [countR, count32, count31]; omega)
    (by simpa [prepared, Activation.forgetRefs, rootsR, roots32, roots31, Roots.set] using unbound 37 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after at finalMachine
  have last3 : Calling.Prefix callee callers headCases (headActions.drop 23) w32 a32 final after :=
    Calling.Prefix.append (suffix := headCases) (rest := [.storageLive 37]) cleanup
      (.cons (Calling.instruction_noncall_run (act := .storageLive 37) live37) (.nil _ _))
  have last5 : Calling.Prefix callee callers headCases (headActions.drop 21) w31 a31 final after :=
    Calling.Prefix.append (suffix := headCases) (rest := headActions.drop 23) run32 last3
  have whole : Calling.Prefix callee callers headCases (headActions.drop 19) world active final after :=
    Calling.Prefix.append (suffix := headCases) (rest := headActions.drop 21) run31 last5
  refine ⟨final, after, whole, finalMachine, countR.trans (count32.trans count31), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1
  · exact (last5.closed_local_same (index := 31) m31.native.valid m31.native.callersValid m31.native.wellFormed
      (by rw [value31]; exact ofValue_typed (option_typed result)) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans value31
  · exact (last3.closed_local_same (index := 32) m32.native.valid m32.native.callersValid m32.native.wellFormed
      (by rw [value32]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans value32
  · simp only [after, Partial.Locals.set, ite_true]
  · exact ⟨root37, by simp [after, Roots.set], (wr.allocate_spec _ _).2.1⟩
  · simp [after, prepared, Activation.forgetRefs, rootsR, Roots.set]
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [after, prepared, Activation.forgetRefs, rootsR, roots32, roots31, Roots.set]
  · intro slot outside
    have different : slot ≠ 31 ∧ slot ≠ 32 ∧ slot ≠ 33 ∧ slot ≠ 37 := by simpa using outside
    simp only [after, prepared, Activation.forgetRefs, rootsR, roots32, roots31, Roots.set,
      different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · intro index binding root raw read
    have other : index ≠ 31 := by intro same; subst index; rw [unbound 31 (by simp)] at root; cases root
    have rootA31 : a31.roots index = some binding := by simpa only [roots31, Roots.set, other, ite_false] using root
    have memory32 := memory32 index binding rootA31 raw (memory31 index binding root raw read)
    have memoryR : wr.memory[binding.address]? = some raw := by rw [memoryR]; exact memory32
    exact (wr.allocate_keeps mr.native.wellFormed _ _ []).memory _ _ memoryR

end SubtreeProofs.Rust.SourceEval.Evaluator
