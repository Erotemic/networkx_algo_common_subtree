module

public import SubtreeProofs.Rust.SourcePairMatchedQueryEntry
public import SubtreeProofs.Rust.SourceOriginalConcatenate

/-! Construct the actual left-concatenation result storage and two original
child-word reborrows. The matched candidate, updated table and original query
snapshots remain valid with all shared aliases permitted. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure LeftConcatArgumentScope (left right : BalancedWord) (world : World) (active : Activation) : Prop where
  leftValue : active.state 72 = .shared (encodeWord left)
  rightValue : active.state 73 = .shared (encodeWord right)
  resultEmpty : active.state 71 = .empty
  resultRoot : ∃ binding, active.roots 71 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  bound : ∀ slot ∈ [71, 72, 73], ∃ binding, active.roots slot = some binding

theorem pair_left_concat_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (queries : PairQueryScope lh lt rh rt active) (candidate : MatchedScope heads tails table total active)
    (count : 74 ≤ active.count) (unbound : ∀ slot ∈ [71, 72, 73], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 35) ((matchedActions.drop 30).take 5) world active final after ∧
      OriginalLoanMachine before callers previous external [73, 72, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      LeftConcatArgumentScope lh lt final after ∧ PairQueryScope lh lt rh rt after ∧ MatchedScope heads tails table total after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [71, 72, 73] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w71, a71, run71, m71, roots71, count71, frame71, empty71, raw71, memory71⟩ :=
    original_open_local_complete h callee (matchedCode 31) (slot := 71) (by decide) (by omega) (unbound 71 (by simp))
  have left71 : a71.state 27 = .shared (.boxed (encodeWord lh)) :=
    (run71.retained_local_same_calls (index := 27) (by decide +kernel) (by decide +kernel)).trans queries.leftHead
  obtain ⟨w72, a72, run72, m72, roots72, count72, frame72, value72, memory72⟩ :=
    original_borrow_view_complete m71 callee (matchedCode 33) (slot := 27) (destination := 72)
      (place := .deref (.deref (.local 27))) (by simp) (by decide) rfl
      (by rw [left71]; exact .shared _ _) (boxed_word_reborrow_source left71) (NativeData.word lh)
      (by rw [count71]; omega) (by simpa [roots71, Roots.set] using unbound 72 (by simp))
  have first3 : Calling.Prefix callee callers (matchedCode 33) ((matchedActions.drop 30).take 3) world active w72 a72 :=
    Calling.Prefix.append (suffix := matchedCode 33) (rest := (matchedActions.drop 31).take 2) run71 run72
  have right72 : a72.state 28 = .shared (.boxed (encodeWord lt)) :=
    (first3.retained_local_same_calls (index := 28) (by decide +kernel) (by decide +kernel)).trans queries.leftTail
  obtain ⟨final, after, run73, machine, roots73, count73, frame73, value73, memory73⟩ :=
    original_borrow_view_complete m72 callee (matchedCode 35) (slot := 28) (destination := 73)
      (place := .deref (.deref (.local 28))) (by simp) (by decide) rfl
      (by rw [right72]; exact .shared _ _) (boxed_word_reborrow_source right72) (NativeData.word lt)
      (by rw [count72, count71]; omega) (by simpa [roots72, roots71, Roots.set] using unbound 73 (by simp))
  have whole : Calling.Prefix callee callers (matchedCode 35) ((matchedActions.drop 30).take 5) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 35) (rest := (matchedActions.drop 33).take 2) first3 run73
  have queryAfter : PairQueryScope lh lt rh rt after := by
    apply prefix_pair_queries_complete whole queries
    · intro slot member
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    · intro slot member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  let root71 : Binding := ⟨world.memory.length, world.memory.length⟩
  have bound71a71 : a71.roots 71 = some root71 := by simp [roots71, root71, Roots.set]
  have bound71a72 : a72.roots 71 = some root71 := by simpa [roots72, Roots.set] using bound71a71
  have last4 : Calling.Prefix callee callers (matchedCode 35) ((matchedActions.drop 31).take 4) w71 a71 final after :=
    Calling.Prefix.append (suffix := matchedCode 35) (rest := (matchedActions.drop 33).take 2) run72 run73
  refine ⟨final, after, whole, machine, ?_, queryAfter, ?_, count73.trans (count72.trans count71), frame73.trans (frame72.trans frame71), ?_, ?_⟩
  · refine ⟨(run73.retained_local_same_calls (index := 72) (by decide +kernel) (by decide +kernel)).trans value72, value73,
      (last4.closed_local_same (index := 71) m71.native.valid m71.native.callersValid m71.native.wellFormed
        (by rw [empty71]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty71,
      ⟨root71, by simpa [roots73, Roots.set] using bound71a72,
        memory73 71 root71 bound71a72 _ (memory72 71 root71 bound71a71 _ raw71)⟩, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> simp [roots73, roots72, roots71, Roots.set]
  · refine ⟨(whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [candidate.headHole]; exact resultWordHole_typed heads.edges) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans candidate.headHole,
      (whole.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [candidate.tailHole]; exact resultWordHole_typed tails.edges) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans candidate.tailHole,
      (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [candidate.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans candidate.tableValue,
      (whole.closed_local_same (index := 58) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [candidate.totalValue]; exact .number total.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans candidate.totalValue,
      (whole.closed_local_same (index := 64) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [candidate.candidate]; exact ofValue_typed (result_typed (matchedWitness heads tails total))) (.adt .embedding)
        (by decide +kernel) (by decide +kernel)).trans candidate.candidate, ?_⟩
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> simp only [roots73, roots72, roots71, Roots.set] <;> exact candidate.retired _ (by simp)
  · intro slot outside
    have different : slot ≠ 71 ∧ slot ≠ 72 ∧ slot ≠ 73 := by simpa using outside
    simp only [roots73, roots72, roots71, Roots.set, different.1, different.2.1, different.2.2, ite_false]
  · intro index binding root raw memoryRead
    have not71 : index ≠ 71 := by intro same; subst index; rw [unbound 71 (by simp)] at root; cases root
    have not72 : index ≠ 72 := by intro same; subst index; rw [unbound 72 (by simp)] at root; cases root
    have rootA71 : a71.roots index = some binding := by simpa only [roots71, Roots.set, not71, ite_false] using root
    have rootA72 : a72.roots index = some binding := by simpa only [roots72, Roots.set, not72, ite_false] using rootA71
    exact memory73 index binding rootA72 _ (memory72 index binding rootA71 _ (memory71 index binding root _ memoryRead))

end SubtreeProofs.Rust.SourceEval.Evaluator
