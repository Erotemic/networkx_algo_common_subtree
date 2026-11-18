module

public import SubtreeProofs.Rust.SourcePairLeftConcatCall
public import SubtreeProofs.Rust.SourceOriginalConcatenateFresh
public import SubtreeProofs.Rust.SourceCallOwnerProvenance

/-! Actual left concatenation derives fresh word owners and preserves the
bounded matched candidate through its call and all three cleanup instructions. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_left_concat_call_complete_fresh {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [73, 72, 45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : LeftConcatArgumentScope lh lt world active) (queries : PairQueryScope lh lt rh rt active)
    (candidate : MatchedScope heads tails table total active) (candidateAbove : LocalOwnersAbove before.memory.length world active 64) (count : 74 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after, ∃ cost : Cost, ∃ nativeCost : LookupSource.Cost,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairQueryScope lh lt rh rt after ∧ MatchedScope heads tails table total after ∧
      after.state 71 = Slot.ofValue (encodeWord (OrderedSolver.appendWord lh lt)) ∧
      (∃ binding, after.roots 71 = some binding) ∧ after.roots 72 = none ∧ after.roots 73 = none ∧
      after.roots = (active.roots.set 73 none).set 72 none ∧ after.count = active.count ∧ after.frame = active.frame ∧
      nativeCost.events = MemoSource.concatenateEvents lh lt ∧
      cost = (Cost.local (Action.call .concatenate (concatenateArgs 72 73) 71).weight).plus (SourceEval.Legacy.costMap nativeCost) ∧
      (∀ slot binding, slot ≠ 71 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) ∧
      LocalOwnersAbove before.memory.length final after 64 ∧ LocalOwnersAbove before.memory.length final after 71 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39) ((matchedActions.drop 35).take 4) world active final after := by
  obtain ⟨fuel, budget, final, after, cost, nativeCost, machine, queriesAfter, candidateAfter, value, root,
    dead72, dead73, rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, stable⟩ :=
    pair_left_concat_call_complete h scope queries candidate count
  have whole := stable fuel budget (by rfl) (by rfl)
  change Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 39)
    (.call .concatenate (concatenateArgs 72 73) 71 :: (matchedActions.drop 36).take 3) world active final after at whole
  cases whole with
  | @cons _ callWorld _ _ callActive _ _ _ work run cleanup =>
    simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a, callWork⟩, called, last⟩ := run
    cases last
    have prepared := h.prepare (matchedCode 35)
    have first : (active.forgetRefs (matchedCode 35)).state 72 = .shared (encodeWord lh) :=
      (Activation.forgetRefs_observed active (matchedCode 35) 72 (by decide +kernel)).trans scope.leftValue
    have second : (active.forgetRefs (matchedCode 35)).state 73 = .shared (encodeWord lt) :=
      (Activation.forgetRefs_observed active (matchedCode 35) 73 (by decide +kernel)).trans scope.rightValue
    have source := concatenate_arguments_source 72 73 (by decide) lh lt first second
    have typed : SnapshotFieldsTyped [.reference (encodeWord lh), .reference (encodeWord lt)] [.shared (.adt .word), .shared (.adt .word)] :=
      .cons (.shared (word_typed lh)) (.cons (.shared (word_typed lt)) .nil)
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
    have candidateKept := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
      prepared.native.valid prepared.native.callersValid prepared.native.wellFormed ready
      (by change 64 < active.count; omega) (by decide +kernel) (candidateAbove.prepare_any (matchedCode 35)) called
    have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) prepared.native.valid
      prepared.native.callersValid prepared.native.wellFormed .concatenate (concatenateArgs 72 73) 71 ready called
    have candidateFinal := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
      checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 candidateKept
    have wordFinal := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
      checked.2.2.2.2.1 checked.2.2.2.2.2.1 checked.2.2.2.2.2.2.1 fresh
    exact ⟨fuel, budget, final, after, cost, nativeCost, machine, queriesAfter, candidateAfter, value, root,
      dead72, dead73, rootsAfter, countAfter, frameAfter, events, costEq, memoryAfter, candidateFinal, wordFinal, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
