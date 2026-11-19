module

public import SubtreeProofs.Rust.SourcePairReturnPacking

/-! Execute the eight real drop/dead instructions for the emptied output
assembly sources, preserving the stored tuple's witness-field provenance. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_return_retirement_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) (result : CommonEmbedding) (table : MemoTable)
    (output : active.state 0 = Slot.ofValue (encodeOutput (some result) table))
    (above : LocalResultOwnersAbove before.memory.length world active 0)
    (empty : ∀ slot ∈ [112, 110, 104, 99], active.state slot = .empty)
    (bound : ∀ slot ∈ [112, 110, 104, 99], ∃ binding, active.roots slot = some binding)
    (held : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot) :
    ∃ final after,
      Calling.Prefix callee callers (finishCode 56) ((finishActions.drop 48).take 8) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 0 = Slot.ofValue (encodeOutput (some result) table) ∧ LocalResultOwnersAbove before.memory.length final after 0 ∧
      (∀ slot ∈ [112, 110, 104, 99], after.state slot = .empty ∧ after.roots slot = none) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ final.memory = world.memory ∧
      (∀ slot, slot ∉ [112, 110, 104, 99] → after.roots slot = active.roots slot) ∧
      (∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot, slot ∉ [112, 110, 104, 99] → (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) := by
  obtain ⟨b112, hb112⟩ := bound 112 (by simp)
  obtain ⟨b110, hb110⟩ := bound 110 (by simp)
  obtain ⟨b104, hb104⟩ := bound 104 (by simp)
  obtain ⟨b99, hb99⟩ := bound 99 (by simp)
  have plan : RetirementPlan active.roots ((finishActions.drop 48).take 8)
      ((((active.roots.set 112 none).set 110 none).set 104 none).set 99 none) :=
    .drop hb112 (.dead hb112
      (.drop (by simpa [Roots.set] using hb110) (.dead (by simpa [Roots.set] using hb110)
        (.drop (by simpa [Roots.set] using hb104) (.dead (by simpa [Roots.set] using hb104)
          (.drop (by simpa [Roots.set] using hb99) (.dead (by simpa [Roots.set] using hb99) (.nil _))))))))
  have zero : ZeroRetirement ((finishActions.drop 48).take 8) active.state := by
    intro slot member
    have temporary : slot ∈ [112, 110, 104, 99] := by simpa [finishActions] using member
    rw [empty slot temporary]; simp only [Slot.dropWork]
  obtain ⟨final, after, run, machine, roots, count, memory⟩ := plan.complete_original callee (finishCode 56) h rfl zero
  have rootOutside : ∀ slot, slot ∉ [112, 110, 104, 99] → after.roots slot = active.roots slot := by
    intro slot outside
    have different : slot ≠ 112 ∧ slot ≠ 110 ∧ slot ≠ 104 ∧ slot ≠ 99 := by simpa using outside
    simp [roots, Roots.set, different.1, different.2.1, different.2.2.1, different.2.2.2]
  refine ⟨final, after, run, machine, ?_, above.memory_same memory (rootOutside 0 (by decide)), ?_, count,
    run.shape.1, memory, rootOutside, ?_, ?_⟩
  · exact (run.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [output]; exact ofValue_typed (encodeOutput_typed (some result) table))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) rfl (by decide +kernel)).trans output
  · intro slot member
    have rootNone : after.roots slot = none := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [roots, Roots.set]
    refine ⟨?_, rootNone⟩
    obtain ⟨_, frame⟩ := machine.native.valid.2
    have mask := frame.slots slot
    change (match after.roots slot with | none => after.state slot = .empty | some binding => _) at mask
    simpa only [rootNone] using mask
  · intro slot member
    exact run.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (held slot member)
  · intro slot outside unshared
    apply run.unshared_local_same h.native.valid h.native.callersValid h.native.wellFormed unshared (by decide +kernel)
    have different : slot ≠ 112 ∧ slot ≠ 110 ∧ slot ≠ 104 ∧ slot ≠ 99 := by simpa using outside
    simp [finishActions, SourceEval.LocalPreservation.action, different.1, different.2.1, different.2.2.1, different.2.2.2]

end SubtreeProofs.Rust.SourceEval.Evaluator
