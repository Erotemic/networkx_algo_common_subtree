module

public import SubtreeProofs.Rust.SourcePairRootScoreProgram

/-! Copy the successful subtotal into its retained scalar local and retire both
the scalar copy temporary and original optional subtotal storage. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RootSubtotalScope (heads tails : CommonEmbedding) (table : MemoTable) (subtotal : Aeneas.Std.U32) (active : Activation) : Prop where
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  subtotalValue : active.state 51 = .number subtotal.val
  retired : ∀ slot ∈ [52, 55], active.roots slot = none

theorem pair_root_subtotal_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : ScoreSumScope heads tails table world active) (subtotal : Aeneas.Std.U32)
    (success : checkedAdd32 heads.edges.val tails.edges.val = some subtotal.val)
    (count : 56 ≤ active.count) (unbound55 : active.roots 55 = none) :
    ∃ final after,
      Calling.Prefix callee callers (rootScoreCode 6) (rootScoreActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootSubtotalScope heads tails table subtotal after ∧
      after.roots = active.roots.set 52 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ index binding, index ≠ 51 → active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have value52 : active.state 52 = Slot.ofValue (encodeNumberOption (some subtotal.val)) := by rw [scope.result, success]
  obtain ⟨w55, a55, first2, m55, roots55, count55, frame55, source55, value55, memory55⟩ :=
    original_number_copy_complete h callee (rootScoreCode 2) (source := 52) (destination := 55) (by decide) (by decide) (by decide)
      value52 (.field (.local 52) (some 1) 0) rfl (number_option_payload_read subtotal.val) subtotal.hmax (by omega) unbound55
  obtain ⟨root51, bound51, raw51⟩ := scope.subtotalRoot
  have bound51a55 : a55.roots 51 = some root51 := by simpa [roots55, Roots.set] using bound51
  have empty51 : a55.state 51 = .empty :=
    (first2.closed_local_same (index := 51) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.subtotalEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.subtotalEmpty
  obtain ⟨wa, aa, assigned, ma, rootsA, countA, frameA, tempA, valueA, memoryA⟩ :=
    original_number_assign_complete m55 callee (rootScoreCode 3) (source := 55) (destination := 51) (by decide) (by decide) (by decide)
      value55 (.local 55) rfl (number_local_read subtotal.val) subtotal.hmax bound51a55 (memory55 51 root51 bound51 _ raw51) empty51
  have bound55 : aa.roots 55 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsA, roots55, Roots.set]
  have plan55 : RetirementPlan aa.roots [.storageDead 55] (aa.roots.set 55 none) := .dead bound55 (.nil _)
  have zero55 : ZeroRetirement [.storageDead 55] aa.state := by
    intro slot member
    have same : slot = 55 := by simpa using member
    subst slot; rw [tempA]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, retire55, mr, rootsR, countR, memoryR⟩ := plan55.complete_original callee (rootScoreCode 4) ma rfl zero55
  let af := ar.forgetRefs (rootScoreCode 4)
  have mf := mr.prepare (rootScoreCode 4)
  have fake : Calling.Prefix callee callers (rootScoreCode 5) [.fakeRead (.local 51)] wr ar wr af :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 51)) rfl) (.nil _ _)
  obtain ⟨root52, bound52⟩ := scope.resultRoot
  have bound52f : af.roots 52 = some root52 := by simpa [af, Activation.forgetRefs, rootsR, rootsA, roots55, Roots.set] using bound52
  have first5 : Calling.Prefix callee callers (rootScoreCode 5) (rootScoreActions.take 5) world active wr af :=
    Calling.Prefix.append (suffix := rootScoreCode 5) (rest := [.fakeRead (.local 51)])
      (Calling.Prefix.append (suffix := rootScoreCode 4) (rest := [.storageDead 55])
        (Calling.Prefix.append (suffix := rootScoreCode 3) (rest := [.assign 51 (.use (.copy (.local 55)))]) first2 assigned) retire55) fake
  have value52f : af.state 52 = Slot.ofValue (encodeNumberOption (some subtotal.val)) :=
    (first5.closed_local_same (index := 52) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [value52]; exact ofValue_typed (.node (.optionSome _) (.cons (.number subtotal.hmax) .nil)))
      (.option .u32) (by decide +kernel) (by decide +kernel)).trans value52
  have plan52 : RetirementPlan af.roots [.storageDead 52] (af.roots.set 52 none) := .dead bound52f (.nil _)
  have zero52 : ZeroRetirement [.storageDead 52] af.state := by
    intro slot member
    have same : slot = 52 := by simpa using member
    subst slot; rw [value52f]; simp [encodeNumberOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  obtain ⟨final, after, retire52, machine, rootsAfter, countAfter, memoryAfter⟩ := plan52.complete_original callee (rootScoreCode 6) mf rfl zero52
  have whole : Calling.Prefix callee callers (rootScoreCode 6) (rootScoreActions.take 6) world active final after :=
    Calling.Prefix.append (suffix := rootScoreCode 6) (rest := [.storageDead 52]) first5 retire52
  have last3 : Calling.Prefix callee callers (rootScoreCode 6) ((rootScoreActions.drop 3).take 3) wa aa final after :=
    Calling.Prefix.append (suffix := rootScoreCode 6) (rest := [.fakeRead (.local 51), .storageDead 52]) retire55
      (Calling.Prefix.append (suffix := rootScoreCode 6) (rest := [.storageDead 52]) fake retire52)
  refine ⟨final, after, whole, machine, ?_, ?_,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).2,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact (whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.headValue]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.headValue
    · exact (whole.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tailValue]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.tailValue
    · exact (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.tableValue
    · exact (last3.closed_local_same (index := 51) ma.native.valid ma.native.callersValid ma.native.wellFormed
        (by rw [valueA]; exact .number subtotal.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans valueA
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [rootsAfter, af, Activation.forgetRefs, rootsR, Roots.set]
  · rw [rootsAfter]
    funext slot
    by_cases same : slot = 55
    · subst slot; simp [af, Activation.forgetRefs, rootsR, Roots.set, unbound55]
    · simp [af, Activation.forgetRefs, rootsR, rootsA, roots55, Roots.set, same]
  · intro index binding different root raw memoryRead
    have not55 : index ≠ 55 := by intro same; subst index; rw [unbound55] at root; cases root
    have rootA55 : a55.roots index = some binding := by simpa only [roots55, Roots.set, not55, ite_false] using root
    rw [memoryAfter, memoryR]
    exact memoryA index binding different rootA55 raw (memory55 index binding root raw memoryRead)

end SubtreeProofs.Rust.SourceEval.Evaluator
