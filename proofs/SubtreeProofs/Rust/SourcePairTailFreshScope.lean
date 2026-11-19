module

public import SubtreeProofs.Rust.SourcePairHeadFreshScope
public import SubtreeProofs.Rust.SourcePairTailScope

/-! The complete actual tail region retains the independently bounded held
head witness and derives the tail optional witness bound. The owned old table
remains unrestricted and both smaller contracts stay explicit. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_tail_scope_complete_fresh {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads : CommonEmbedding} {table : MemoTable}
    (scope : PairHeadScope initial lh lt rh rt (some heads) table world active)
    (support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → initial.roots slot = none)
    (count : 48 ≤ active.count) (childTotal : NativeTotalFresh lt rt)
    (headsAbove : LocalOwnersAbove before.memory.length world active 31) :
    ∃ minimumFuel minimumBudget final after result output,
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      PairTailScope active lh lt rh rt heads result output final after ∧
      memoized_common_embedding lt rt table = .ok (result, output) ∧
      LocalOwnersAbove before.memory.length final after 37 ∧ LocalOwnersAbove before.memory.length final after 41 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions world active final after := by
  obtain ⟨fuel, budget, final, after, result, output, machine, finalScope, native, stable⟩ :=
    pair_tail_scope_complete h scope support count childTotal.total
  have whole := stable fuel budget (by rfl) (by rfl)
  have unbound : ∀ slot ∈ [38, 43, 44, 45, 46], active.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> rw [scope.otherRoots _ (by decide)] <;> exact support _ (by decide)
  obtain ⟨wp, ap, payloadRun, mp, rootsP, countP, _, _, _, tableP, leftP, rightP, _⟩ :=
    tail_head_payload_complete h (Recursive.original budget fuel) scope (by omega) (unbound 38 (by simp))
  have payloadFresh := optional_payload_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed
    (by decide) (by decide) headsAbove payloadRun
  have tupleP : ap.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) :=
    (payloadRun.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  obtain ⟨wa, aa, arguments, ma, argumentScope, _⟩ :=
    pair_tail_arguments_complete mp (Recursive.original budget fuel) tupleP leftP rightP tableP (by rw [countP]; omega)
      (by intro slot member; rw [rootsP]; exact unbound slot (List.mem_cons_of_mem _ member))
  have headsA := arguments.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    mp.native.valid mp.native.callersValid mp.native.wellFormed payloadFresh
  have first13 : Calling.Prefix (Recursive.original budget fuel) callers (tailCode 13) (tailActions.take 13) world active wa aa :=
    Calling.Prefix.append (suffix := tailCode 13) (rest := (tailActions.drop 6).take 7) payloadRun arguments
  have splitWhole : Calling.Prefix (Recursive.original budget fuel) callers tailCases
      ((tailActions.take 13) ++ tailActions.drop 13) world active final after := by
    simpa only [List.take_append_drop] using whole
  obtain ⟨argumentWorld, argumentActive, actualArguments, remaining⟩ := splitWhole.split
  have same := first13.unique actualArguments
  have am := ma
  rw [same.1, same.2] at am headsA
  have argScope := argumentScope
  rw [same.1, same.2] at argScope
  change Calling.Prefix (Recursive.original budget fuel) callers tailCases
    (.call .evaluate (nativeCallArgs 44 45 46) 43 :: tailActions.drop 14) argumentWorld argumentActive final after at remaining
  cases remaining with
  | @cons _ callWorld _ _ callActive _ _ _ cost run cleanup =>
    simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨w, a, work⟩, called, last⟩ := run
    cases last
    let observed := argumentActive.forgetRefs (tailCode 13)
    have prepared := am.prepare (tailCode 13)
    have left : observed.state 44 = .shared (encodeWord lt) :=
      (Activation.forgetRefs_observed argumentActive (tailCode 13) 44 (by decide +kernel)).trans argScope.left
    have right : observed.state 45 = .shared (encodeWord rt) :=
      (Activation.forgetRefs_observed argumentActive (tailCode 13) 45 (by decide +kernel)).trans argScope.right
    have tableValue : observed.state 46 = Slot.ofValue (encodeTable table) :=
      (LoanEnding.forget_closed _ _ (by rw [argScope.table]; exact ofValue_typed (table_typed table)) (.adt .table)).trans argScope.table
    have source := native_call_arguments 44 45 46 (by decide) (by decide) (by decide) lt rt table left right tableValue
    obtain ⟨actualResult, actualTable, state, _, callValid, callersValid, callWellFormed, fresh⟩ :=
      Derived.evaluator_checkpoint_fresh_spec prepared.native.valid prepared.native.callersValid prepared.native.wellFormed
        prepared.native.ownerFrame prepared.native.coverage lt rt table childTotal source called
    have typed : SnapshotFieldsTyped [.reference (encodeWord lt), .reference (encodeWord rt), encodeTable table]
        [.shared (.adt .word), .shared (.adt .word), .adt .table] :=
      .cons (.shared (word_typed lt)) (.cons (.shared (word_typed rt)) (.cons (table_typed table) .nil))
    have outputType : Types.callOutput .evaluate [.shared (.adt .word), .shared (.adt .word), .adt .table] =
        some (.tuple [.adt .optional, .adt .table]) := by
      simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
    have ready := Derived.call_ready_from_values (callers := callers) prepared.native.valid source typed outputType
    have headKept := Derived.call_keeps_owner_provenance (Recursive.original_typed_respects budget fuel)
      prepared.native.valid prepared.native.callersValid prepared.native.wellFormed ready
      (by change 37 < argumentActive.count; rw [actualArguments.shape.2.1]; omega) (by decide +kernel)
      (headsA.prepare_any (tailCode 13)) called
    have headsAfter := cleanup.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
      callValid callersValid callWellFormed headKept
    have value : a.state 43 = Slot.ofValue (encodeOutput actualResult actualTable) := by
      rw [state]; simp only [Partial.Locals.set, ite_true]
    have cleanupShape : Calling.Prefix (Recursive.original budget fuel) callers tailCases
        ([46, 45, 44].map Action.storageDead ++
          ([.storageLive 41, .assign 41 (.use (.move (.field (.local 43) none 0)))] ++ tailActions.drop 19)) w a final after := cleanup
    have tailFresh := cleanupShape.retire_unpack_result_owner_provenance callValid callersValid callWellFormed
      (by decide) (by decide) value (fresh.weaken prepared.native.memoryBound) (by decide +kernel) (by decide +kernel)
    exact ⟨fuel, budget, final, after, result, output, machine, finalScope, native, headsAfter, tailFresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
