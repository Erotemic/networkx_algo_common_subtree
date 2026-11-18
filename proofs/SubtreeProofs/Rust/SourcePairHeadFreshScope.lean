module

public import SubtreeProofs.Rust.SourceCallOwnerProvenance
public import SubtreeProofs.Rust.SourceOptionalPayloadOwnerProvenance
public import SubtreeProofs.Rust.SourcePairHeadScope

/-! Complete actual head-region execution additionally derives the optional
witness owner bound from the explicit stronger smaller head-request contract.
Old table owners and legal original query/caller aliases remain unrestricted. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_head_scope_complete_fresh {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : MissScope initial (.Pair lh lt) (.Pair rh rt) table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 38 ≤ active.count)
    (childTotal : NativeTotalFresh lh rh) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairHeadScope active lh lt rh rt result output final after ∧
      memoized_common_embedding lh rh table = .ok (result, output) ∧
      LocalOwnersAbove before.memory.length final after 31 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions world active final after := by
  obtain ⟨fuel, budget, final, after, result, output, machine, finalScope, native, stable⟩ :=
    pair_head_scope_complete h scope unbound count childTotal.total
  have whole := stable fuel budget (by rfl) (by rfl)
  obtain ⟨wv, av, views, mv, countV, _, _, otherV, tupleV, tableV, leftV, _, rightV, _, _⟩ :=
    pair_head_views_complete h (Recursive.original budget fuel) scope unbound (by omega)
  have unboundV : ∀ slot ∈ [33, 34, 35, 36], av.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rw [otherV _ (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨wa, aa, arguments, ma, argumentScope, _⟩ :=
    pair_head_arguments_complete mv (Recursive.original budget fuel) tupleV leftV rightV tableV (by rw [countV]; omega) unboundV
  have first15 : Calling.Prefix (Recursive.original budget fuel) callers (headCode 15) (headActions.take 15) world active wa aa :=
    Calling.Prefix.append (suffix := headCode 15) (rest := (headActions.drop 8).take 7) views arguments
  have splitWhole : Calling.Prefix (Recursive.original budget fuel) callers headCases
      ((headActions.take 15) ++ headActions.drop 15) world active final after := by
    simpa only [List.take_append_drop] using whole
  obtain ⟨argumentWorld, argumentActive, actualArguments, remaining⟩ := splitWhole.split
  have same := first15.unique actualArguments
  have am := ma
  rw [same.1, same.2] at am
  have argScope := argumentScope
  rw [same.1, same.2] at argScope
  change Calling.Prefix (Recursive.original budget fuel) callers headCases
    (.call .evaluate headArgs 33 :: headActions.drop 16) argumentWorld argumentActive final after at remaining
  cases remaining with
  | @cons _ callWorld _ _ callActive _ _ _ cost run cleanup =>
    simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a, work⟩, called, last⟩ := run
    cases last
    let observed := argumentActive.forgetRefs (headCode 15)
    have prepared := am.prepare (headCode 15)
    have left : observed.state 34 = .shared (encodeWord lh) :=
      (Activation.forgetRefs_observed argumentActive (headCode 15) 34 (by decide +kernel)).trans argScope.left
    have right : observed.state 35 = .shared (encodeWord rh) :=
      (Activation.forgetRefs_observed argumentActive (headCode 15) 35 (by decide +kernel)).trans argScope.right
    have tableValue : observed.state 36 = Slot.ofValue (encodeTable table) :=
      (LoanEnding.forget_closed _ _ (by rw [argScope.table]; exact ofValue_typed (table_typed table)) (.adt .table)).trans argScope.table
    have source := head_call_arguments lh rh table left right tableValue
    obtain ⟨actualResult, actualTable, state, _, callValid, callersValid, callWellFormed, fresh⟩ :=
      Derived.evaluator_checkpoint_fresh_spec prepared.native.valid prepared.native.callersValid prepared.native.wellFormed
        prepared.native.ownerFrame prepared.native.coverage lh rh table childTotal source called
    have value : a.state 33 = Slot.ofValue (encodeOutput actualResult actualTable) := by
      rw [state]; simp only [Partial.Locals.set, ite_true]
    have cleanupShape : Calling.Prefix (Recursive.original budget fuel) callers headCases
        ([36, 35, 34].map Action.storageDead ++
          ([.storageLive 31, .assign 31 (.use (.move (.field (.local 33) none 0)))] ++ headActions.drop 21))
        w a final after := cleanup
    have selected := cleanupShape.retire_unpack_result_owner_provenance callValid callersValid callWellFormed
      (by decide) (by decide) value (fresh.weaken prepared.native.memoryBound) (by decide +kernel) (by decide +kernel)
    exact ⟨fuel, budget, final, after, result, output, machine, finalScope, native, selected, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
