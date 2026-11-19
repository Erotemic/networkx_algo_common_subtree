module

public import SubtreeProofs.Rust.SourcePairRightConcatCall
public import SubtreeProofs.Rust.SourceOriginalConcatenateFresh
public import SubtreeProofs.Rust.SourceCallOwnerProvenance

/-! The real right concatenation derives a bounded owned word while retaining
all previously bounded held witnesses and the left query through cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_right_concat_call_complete_provenance {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [87, 86, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : RightConcatArgumentScope rh rt world active)
    (payload : RightPayloadScope lh lt rh rt heads tails left table total active) (heldAbove : ∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length world active slot)
    (count : 88 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RightPayloadScope lh lt rh rt heads tails left table total after ∧
      after.state 85 = Slot.ofValue (encodeWord (OrderedSolver.appendWord rh rt)) ∧
      (∃ binding, after.roots 85 = some binding) ∧ after.roots 86 = none ∧ after.roots 87 = none ∧
      after.roots = (active.roots.set 87 none).set 86 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      nativeCost.events = MemoSource.concatenateEvents rh rt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 86 87) 85).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ 85 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      (∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length final after slot) ∧
      LocalOwnersAbove before.memory.length final after 85 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15) ((rightActions.drop 11).take 4) world active final after := by
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, root,
    dead72, dead73, rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, stable⟩ :=
    pair_right_concat_call_complete h scope payload count
  have whole := stable fuel budget (by rfl) (by rfl)
  change Calling.Prefix (Recursive.original budget fuel) callers (rightCode 15)
    (.call .concatenate (concatenateArgs 86 87) 85 :: (rightActions.drop 12).take 3) world active final after at whole
  cases whole with
  | @cons _ callWorld _ _ callActive _ _ _ work run cleanup =>
    simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a, callWork⟩, called, last⟩ := run
    cases last
    have prepared := h.prepare (rightCode 11)
    have first : (active.forgetRefs (rightCode 11)).state 86 = .shared (encodeWord rh) :=
      (Activation.forgetRefs_observed active (rightCode 11) 86 (by decide +kernel)).trans scope.leftValue
    have second : (active.forgetRefs (rightCode 11)).state 87 = .shared (encodeWord rt) :=
      (Activation.forgetRefs_observed active (rightCode 11) 87 (by decide +kernel)).trans scope.rightValue
    have source := concatenate_arguments_source 86 87 (by decide) rh rt first second
    have typed : SnapshotFieldsTyped [.reference (encodeWord rh), .reference (encodeWord rt)] [.shared (.adt .word), .shared (.adt .word)] :=
      .cons (.shared (word_typed rh)) (.cons (.shared (word_typed rt)) .nil)
    have output : Types.callOutput .concatenate [.shared (.adt .word), .shared (.adt .word)] = some (.adt .word) := by
      simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
    have ready := Derived.call_ready_from_values (callers := callers) prepared.native.valid source typed output
    have positive : 0 < fuel := by
      cases fuel with
      | zero =>
        simp only [Derived.call, bind, Option.bind_eq_some_iff] at called
        obtain ⟨_, _, _, _, _, _, _, _, _, _, _, impossible, _⟩ := called
        cases impossible
      | succ n => omega
    have fresh := (Derived.original_helper_call_fresh_output fuel budget positive prepared.native.valid prepared.native.callersValid
      prepared.native.wellFormed (by simp [Helpers.FreshOutputHelper]) ready called).weaken prepared.native.memoryBound
    have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) prepared.native.valid
      prepared.native.callersValid prepared.native.wellFormed .concatenate (concatenateArgs 86 87) 85 ready called
    have heldFinal : ∀ slot ∈ [64, 71, 81], LocalOwnersAbove before.memory.length final after slot := by
      intro slot member
      have slotBound : slot < active.count := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> omega
      have safe : LocalPreservation.action slot (.call .concatenate (concatenateArgs 86 87) 85) = true := by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide +kernel
      have kept := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
        prepared.native.valid prepared.native.callersValid prepared.native.wellFormed ready slotBound safe
        ((heldAbove slot member).prepare_any (rightCode 11)) called
      exact cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> decide +kernel))
        checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 kept
    have wordFinal := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
      checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 fresh
    exact ⟨fuel, budget, final, after, cost, nativeCost, machine, payloadAfter, value, root,
      dead72, dead73, rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, heldFinal, wordFinal, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
