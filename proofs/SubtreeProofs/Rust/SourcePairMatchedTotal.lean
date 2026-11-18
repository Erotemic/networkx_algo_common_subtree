module

public import SubtreeProofs.Rust.SourcePairMatchedProgram

/-! Copy the successful root score into its retained total local and retire the
scalar temporary and original root-score option before matched construction. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure MatchedTotalScope (heads tails : CommonEmbedding) (table : MemoTable) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  totalValue : active.state 58 = .number total.val
  retired : ∀ slot ∈ [59, 61], active.roots slot = none

theorem pair_matched_total_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootScoreScope heads tails table subtotal world active) (total : Aeneas.Std.U32)
    (success : checkedAdd32 subtotal.val 1 = some total.val)
    (count : 62 ≤ active.count) (unbound61 : active.roots 61 = none) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 6) (matchedActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedTotalScope heads tails table total after ∧
      after.roots = active.roots.set 59 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ index binding, index ≠ 58 → active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have value59 : active.state 59 = Slot.ofValue (encodeNumberOption (some total.val)) := by rw [scope.result, success]
  obtain ⟨w61, a61, first2, m61, roots61, count61, frame61, source61, value61, memory61⟩ :=
    original_number_copy_complete h callee (matchedCode 2) (source := 59) (destination := 61) (by decide) (by decide) (by decide)
      value59 (.field (.local 59) (some 1) 0) rfl (number_option_payload_read total.val) total.hmax (by omega) unbound61
  obtain ⟨root58, bound58, raw58⟩ := scope.totalRoot
  have bound58a61 : a61.roots 58 = some root58 := by simpa [roots61, Roots.set] using bound58
  have empty58 : a61.state 58 = .empty :=
    (first2.closed_local_same (index := 58) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.totalEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.totalEmpty
  obtain ⟨wa, aa, assigned, ma, rootsA, countA, frameA, tempA, valueA, memoryA⟩ :=
    original_number_assign_complete m61 callee (matchedCode 3) (source := 61) (destination := 58) (by decide) (by decide) (by decide)
      value61 (.local 61) rfl (number_local_read total.val) total.hmax bound58a61 (memory61 58 root58 bound58 _ raw58) empty58
  have bound61 : aa.roots 61 = some ⟨world.memory.length, world.memory.length⟩ := by simp [rootsA, roots61, Roots.set]
  have plan61 : RetirementPlan aa.roots [.storageDead 61] (aa.roots.set 61 none) := .dead bound61 (.nil _)
  have zero61 : ZeroRetirement [.storageDead 61] aa.state := by
    intro slot member
    have same : slot = 61 := by simpa using member
    subst slot; rw [tempA]; simp only [Slot.dropWork]
  obtain ⟨wr, ar, retire61, mr, rootsR, countR, memoryR⟩ := plan61.complete_original callee (matchedCode 4) ma rfl zero61
  let af := ar.forgetRefs (matchedCode 4)
  have mf := mr.prepare (matchedCode 4)
  have fake : Calling.Prefix callee callers (matchedCode 5) [.fakeRead (.local 58)] wr ar wr af :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 58)) rfl) (.nil _ _)
  obtain ⟨root59, bound59⟩ := scope.resultRoot
  have bound59f : af.roots 59 = some root59 := by simpa [af, Activation.forgetRefs, rootsR, rootsA, roots61, Roots.set] using bound59
  have first5 : Calling.Prefix callee callers (matchedCode 5) (matchedActions.take 5) world active wr af :=
    Calling.Prefix.append (suffix := matchedCode 5) (rest := [.fakeRead (.local 58)])
      (Calling.Prefix.append (suffix := matchedCode 4) (rest := [.storageDead 61])
        (Calling.Prefix.append (suffix := matchedCode 3) (rest := [.assign 58 (.use (.copy (.local 61)))]) first2 assigned) retire61) fake
  have value59f : af.state 59 = Slot.ofValue (encodeNumberOption (some total.val)) :=
    (first5.closed_local_same (index := 59) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [value59]; exact ofValue_typed (.node (.optionSome _) (.cons (.number total.hmax) .nil)))
      (.option .u32) (by decide +kernel) (by decide +kernel)).trans value59
  have plan59 : RetirementPlan af.roots [.storageDead 59] (af.roots.set 59 none) := .dead bound59f (.nil _)
  have zero59 : ZeroRetirement [.storageDead 59] af.state := by
    intro slot member
    have same : slot = 59 := by simpa using member
    subst slot; rw [value59f]; simp [encodeNumberOption, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus]
  obtain ⟨final, after, retire59, machine, rootsAfter, countAfter, memoryAfter⟩ := plan59.complete_original callee (matchedCode 6) mf rfl zero59
  have whole : Calling.Prefix callee callers (matchedCode 6) (matchedActions.take 6) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 6) (rest := [.storageDead 59]) first5 retire59
  have last3 : Calling.Prefix callee callers (matchedCode 6) ((matchedActions.drop 3).take 3) wa aa final after :=
    Calling.Prefix.append (suffix := matchedCode 6) (rest := [.fakeRead (.local 58), .storageDead 59]) retire61
      (Calling.Prefix.append (suffix := matchedCode 6) (rest := [.storageDead 59]) fake retire59)
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
    · exact (last3.closed_local_same (index := 58) ma.native.valid ma.native.callersValid ma.native.wellFormed
        (by rw [valueA]; exact .number total.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans valueA
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [rootsAfter, af, Activation.forgetRefs, rootsR, Roots.set]
  · rw [rootsAfter]
    funext slot
    by_cases same : slot = 61
    · subst slot; simp [af, Activation.forgetRefs, rootsR, Roots.set, unbound61]
    · simp [af, Activation.forgetRefs, rootsR, rootsA, roots61, Roots.set, same]
  · intro index binding different root raw memoryRead
    have not61 : index ≠ 61 := by intro same; subst index; rw [unbound61] at root; cases root
    have rootA61 : a61.roots index = some binding := by simpa only [roots61, Roots.set, not61, ite_false] using root
    rw [memoryAfter, memoryR]
    exact memoryA index binding different rootA61 raw (memory61 index binding root raw memoryRead)

end SubtreeProofs.Rust.SourceEval.Evaluator
