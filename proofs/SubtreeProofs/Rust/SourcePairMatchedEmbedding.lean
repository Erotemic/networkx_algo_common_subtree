module

public import SubtreeProofs.Rust.SourcePairMatchedWord

/-! Attach the retained native total to the owned pair word, constructing the
actual matched embedding. All moved-out word/score temporaries are retired. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def matchedWitness (heads tails : CommonEmbedding) (total : Aeneas.Std.U32) : CommonEmbedding :=
  ⟨.Pair heads.word tails.word, total⟩

structure MatchedScope (heads tails : CommonEmbedding) (table : MemoTable) (total : Aeneas.Std.U32)
    (active : Activation) : Prop where
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  totalValue : active.state 58 = .number total.val
  candidate : active.state 64 = Slot.ofValue (encodeResult (matchedWitness heads tails total))
  retired : ∀ slot ∈ [65, 70], active.roots slot = none

theorem pair_matched_embedding_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : MatchedWordScope heads tails table total world active) (count : 71 ≤ active.count) (unbound70 : active.roots 70 = none) :
    ∃ final after,
      Calling.Prefix callee callers (matchedCode 30) ((matchedActions.drop 23).take 7) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails table total after ∧ after.roots = active.roots.set 65 none ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot binding, slot ≠ 64 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨wp, ap, copied, mp, rootsP, countP, frameP, totalP, valueP, memoryP⟩ :=
    original_number_copy_complete h callee (matchedCode 25) (source := 58) (destination := 70) (by decide) (by decide) (by decide)
      scope.totalValue (.local 58) rfl (number_local_read total.val) total.hmax (by omega) unbound70
  have wordP : ap.state 65 = Slot.ofValue (encodeWord (.Pair heads.word tails.word)) :=
    (copied.closed_local_same (index := 65) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.wordValue]; exact ofValue_typed (word_typed (.Pair heads.word tails.word))) (.adt .word)
      (by decide +kernel) (by decide +kernel)).trans scope.wordValue
  obtain ⟨root64, bound64, raw64⟩ := scope.candidateRoot
  have bound64P : ap.roots 64 = some root64 := by simpa [rootsP, Roots.set] using bound64
  have empty64P : ap.state 64 = .empty :=
    (copied.closed_local_same (index := 64) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.candidateEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.candidateEmpty
  obtain ⟨wa, aa, assigned, ma, rootsA, countA, frameA, empty65, empty70, candidateA, closedA, memoryA⟩ :=
    original_aggregate_two_complete mp callee (matchedCode 26) 65 70 64 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (encodeWord (.Pair heads.word tails.word)) (.number total.val)
      wordP (by simpa only [Slot.ofValue] using valueP) .embedding 0 (result_typed (matchedWitness heads tails total)) (.adt .embedding)
      bound64P (memoryP 64 root64 bound64 _ raw64) empty64P
  obtain ⟨root65, bound65⟩ := Activation.root_of_materialize (value := encodeWord (.Pair heads.word tails.word)) h.native.valid
    (by rw [scope.wordValue]; exact Slot.materialize_ofValue _)
  have bound65A : aa.roots 65 = some root65 := by simpa [rootsA, rootsP, Roots.set] using bound65
  let root70 : Binding := ⟨world.memory.length, world.memory.length⟩
  have bound70A : aa.roots 70 = some root70 := by simp [root70, rootsA, rootsP, Roots.set]
  have plan : RetirementPlan aa.roots ((matchedActions.drop 26).take 3) ((aa.roots.set 70 none).set 65 none) :=
    .dead bound70A (.drop (binding := root65) (by simpa [Roots.set] using bound65A)
      (.dead (binding := root65) (by simpa [Roots.set] using bound65A) (.nil _)))
  have zero : ZeroRetirement ((matchedActions.drop 26).take 3) aa.state := by
    intro slot member
    have selected : slot = 70 ∨ slot = 65 := by simp [matchedActions] at member; omega
    rcases selected with rfl | rfl
    · rw [empty70]; simp only [Slot.dropWork]
    · rw [empty65]; simp only [Slot.dropWork]
  obtain ⟨final, ar, retired, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (matchedCode 29) ma rfl zero
  let after := ar.forgetRefs (matchedCode 29)
  have machine := mr.prepare (matchedCode 29)
  have fake : Calling.Prefix callee callers (matchedCode 30) [.fakeRead (.local 64)] final ar final after :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 64)) rfl) (.nil _ _)
  have last4 : Calling.Prefix callee callers (matchedCode 30) ((matchedActions.drop 26).take 4) wa aa final after :=
    Calling.Prefix.append (suffix := matchedCode 30) (rest := [.fakeRead (.local 64)]) retired fake
  have whole : Calling.Prefix callee callers (matchedCode 30) ((matchedActions.drop 23).take 7) world active final after :=
    Calling.Prefix.append (suffix := matchedCode 30) (rest := (matchedActions.drop 25).take 5) copied
      (Calling.Prefix.append (suffix := matchedCode 30) (rest := (matchedActions.drop 26).take 4) assigned last4)
  refine ⟨final, after, whole, machine, ?_, ?_,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).2,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1, ?_⟩
  · refine ⟨(whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.headHole]; exact resultWordHole_typed heads.edges) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.headHole,
      (whole.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tailHole]; exact resultWordHole_typed tails.edges) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.tailHole,
      (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.tableValue,
      (whole.closed_local_same (index := 58) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.totalValue]; exact .number total.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans scope.totalValue, ?_, ?_⟩
    · have value : aa.state 64 = Slot.ofValue (encodeResult (matchedWitness heads tails total)) := candidateA
      exact (last4.closed_local_same (index := 64) ma.native.valid ma.native.callersValid ma.native.wellFormed
        (by rw [value]; exact ofValue_typed (result_typed (matchedWitness heads tails total))) (.adt .embedding)
        (by decide +kernel) (by decide +kernel)).trans value
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp [after, Activation.forgetRefs, rootsR, Roots.set]
  · change ar.roots = active.roots.set 65 none
    rw [rootsR, rootsA, rootsP]
    funext slot
    by_cases same : slot = 70
    · subst slot; simp [Roots.set, unbound70]
    · simp [Roots.set, same]
  · intro slot binding different root raw memoryRead
    have not70 : slot ≠ 70 := by intro same; subst slot; rw [unbound70] at root; cases root
    have rootP : ap.roots slot = some binding := by simpa only [rootsP, Roots.set, not70, ite_false] using root
    rw [memoryR]
    exact memoryA slot binding different rootP _ (memoryP slot binding root _ memoryRead)

end SubtreeProofs.Rust.SourceEval.Evaluator
