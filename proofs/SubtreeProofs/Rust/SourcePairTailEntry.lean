module

public import SubtreeProofs.Rust.SourcePairTailPrefix

/-! Parsed native pair/pair miss entry through the actual head and tail calls.
Both recursive premises are universal native contracts for strictly smaller
requests; all caller-side instructions and shared sufficient bounds compose. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_tail_prefix_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads : MemoTable) (heads : CommonEmbedding) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotal lh rh) (tailsTotal : NativeTotal lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads)) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive final after result output,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      PairHeadScope missActive lh lt rh rt (some heads) afterHeads headWorld headActive ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.state 43 = Slot.ofValue (encodeOutput result output) ∧ after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 31 = headPayloadHole ∧ after.state 32 = .empty ∧
      memoized_common_embedding lt rt afterHeads = .ok (result, output) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (tailCode 14) (tailActions.take 14) headWorld headActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, resultH, outputH,
    entryRun, missScope, headMachine, headScope, headNative, inspection, prefixes⟩ :=
    entry_pair_head_scope_complete hw hc view lh lt rh rt table leftCell rightCell tableCell leftRead rightRead tableRead
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
  obtain ⟨tailFuel, tailBudget, final, after, result, output, machine, _, _, resultValue, headValue, hole, emptyTable, _, _, _, _, _, _, _, _, _, _, native, _, _, _, stable⟩ :=
    pair_tail_prefix_complete headMachine headScope support (by rw [headScope.count, missScope.count, count]; decide) tailsTotal
  refine ⟨entered, active, max minFuel tailFuel, max minBudget tailBudget, lookupWorld, lookupActive, missWorld, missActive,
    headWorld, headActive, final, after, result, output, entryRun, headScope, machine, resultValue, headValue, hole, emptyTable, native, ?_⟩
  intro fuel budget fuelBound budgetBound
  obtain ⟨common, setup, headPrefix⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
  exact ⟨common, setup, headPrefix, stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
