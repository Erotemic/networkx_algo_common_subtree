module

public import SubtreeProofs.Rust.SourcePairScoreFreshScope

/-! Parsed native pair/pair miss entry through head/tail success and the full
subtotal prefix. Smaller recursive contracts and independent native equations
select the path; all actual prefix worlds share sufficient stable bounds. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_score_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      PairTailScope headActive lh lt rh rt heads (some tails) output tailWorld tailActive ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      ScoreSumScope heads tails output final after ∧
      after.state 52 = Slot.ofValue (encodeNumberOption ((Aeneas.Std.U32.checked_add heads.edges tails.edges).map (fun value => value.val))) ∧
      Derived.scrutinee final after callers (.discriminant (.local 52)) =
        some (numberKey (checkedAdd32 heads.edges.val tails.edges.val), after) ∧
      LocalOwnersAbove world.memory.length final after 37 ∧ LocalOwnersAbove world.memory.length final after 47 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, resultH, outputH,
    entryRun, missScope, headMachine, headScope, headNative, inspection, headFresh, prefixes⟩ :=
    entry_pair_head_scope_complete_fresh hw hc view lh lt rh rt table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered miss headsTotal
  obtain ⟨sameResult, sameOutput⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (headNative.symm.trans headSuccess))
  subst resultH
  subst outputH
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, count, unbound, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  have support : ∀ slot, slot ∉ [0, 1, 2, 3, 13] → missActive.roots slot = none := by
    intro slot outside
    rw [missScope.otherRoots slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)]
    exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  obtain ⟨tailFuel, tailBudget, tailWorld, tailActive, resultT, outputT, tailMachine, tailScope, tailNative, headsKept, tailsFresh, tailStable⟩ :=
    pair_tail_scope_complete_fresh headMachine headScope support (by rw [headScope.count, missScope.count, count]; decide) tailsTotal headFresh
  obtain ⟨sameResult, sameOutput⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (tailNative.symm.trans tailSuccess))
  subst resultT
  subst outputT
  have unboundScore : ∀ slot ∈ [48, 51, 52, 53, 54], tailActive.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;>
      rw [tailScope.otherRoots _ (by decide), headScope.otherRoots _ (by decide)] <;> exact support _ (by decide)
  obtain ⟨scoreFuel, scoreBudget, final, after, machine, scoreScope, _, _, _, _, scoreInspection, headsScore, tailsScore, scoreStable⟩ :=
    pair_score_scope_complete_fresh tailMachine tailScope headsKept tailsFresh (by rw [tailScope.count, headScope.count, missScope.count, count]; decide) unboundScore
  refine ⟨entered, active, max (max minFuel tailFuel) scoreFuel, max (max minBudget tailBudget) scoreBudget,
    lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, tailWorld, tailActive, final, after,
    entryRun, tailScope, machine, scoreScope, ?_, scoreInspection, headsScore, tailsScore, ?_⟩
  · simpa only [checkedAdd32_native] using scoreScope.result
  · intro fuel budget fuelBound budgetBound
    have prefixFuel := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans fuelBound)
    have prefixBudget := (Nat.le_max_left _ _).trans ((Nat.le_max_left _ _).trans budgetBound)
    obtain ⟨common, setup, headPrefix⟩ := prefixes fuel budget prefixFuel prefixBudget
    exact ⟨common, setup, headPrefix,
      tailStable fuel budget ((Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans fuelBound))
        ((Nat.le_max_right _ _).trans ((Nat.le_max_left _ _).trans budgetBound)),
      scoreStable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
