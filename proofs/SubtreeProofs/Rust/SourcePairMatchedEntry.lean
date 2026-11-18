module

public import SubtreeProofs.Rust.SourcePairMatchedScope

/-! Parsed native pair/pair entry through the actual matched candidate. Every
prefix and native successful root-result inspection is constructed from inputs
and explicit smaller contracts; concatenation storage remains fresh. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_matched_scope_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord (.Pair lh lt))))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord (.Pair rh rt))))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (miss : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) = none)
    (headsTotal : NativeTotal lh rh) (tailsTotal : NativeTotal lt rt)
    (headSuccess : memoized_common_embedding lh rh table = .ok (some heads, afterHeads))
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive rootWorld rootActive final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      MatchedScope heads tails output total after ∧ after.count = CallingCertificate.originalEvaluator.source.localCount ∧
      (∀ slot ∈ [59, 61, 65, 66, 67, 68, 69, 70], after.roots slot = none) ∧
      (∀ slot ∈ [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], after.roots slot = none) ∧
      Derived.scrutinee rootWorld rootActive callers (.discriminant (.local 59)) = some (.variant .optional 1, rootActive) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive rootWorld rootActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers (matchedCode 30) (matchedActions.take 30) rootWorld rootActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, entryRun, rootMachine, rootScope, rootValue, rootInspection, prefixes⟩ :=
    entry_pair_root_score_scope_complete hw hc view lh lt rh rt table afterHeads output heads tails subtotal leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess subtotalSuccess
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, count, unbound, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨common, setup, head, tail, score, root⟩ := prefixes minFuel minBudget (by rfl) (by rfl)
  have sameCount : rootActive.count = active.count := root.shape.2.1.trans
    (score.shape.2.1.trans (tail.shape.2.1.trans (head.shape.2.1.trans (setup.shape.2.1.trans common.shape.2.1))))
  have unboundAll : ∀ slot ∈ [61, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81], rootActive.roots slot = none := by
    intro slot member
    have preserves : ∀ actions ∈ [commonPrefix, missSetupActions, headActions, tailActions, scoreActions, rootScoreActions],
        ∀ act ∈ actions, keepsRoot slot act := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
    rw [root.shape.2.2 slot (preserves rootScoreActions (by simp)), score.shape.2.2 slot (preserves scoreActions (by simp)),
      tail.shape.2.2 slot (preserves tailActions (by simp)), head.shape.2.2 slot (preserves headActions (by simp)),
      setup.shape.2.2 slot (preserves missSetupActions (by simp)), common.shape.2.2 slot (preserves commonPrefix (by simp))]
    exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                           rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨matchedFuel, matchedBudget, final, after, machine, matchedScope, countAfter, _, retired, rootsAfter, _, stable⟩ :=
    pair_matched_scope_complete rootMachine rootScope total rootSuccess (by rw [sameCount, count]; decide)
      (by intro slot member; exact unboundAll slot (List.mem_append_left [71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81] member))
  have native : checkedAdd32 subtotal.val 1 = some total.val := by
    have equation := checkedAdd32_native subtotal 1#u32
    rw [rootSuccess] at equation
    exact equation
  refine ⟨entered, active, max minFuel matchedFuel, max minBudget matchedBudget,
    lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive, tailWorld, tailActive, scoreWorld, scoreActive,
    rootWorld, rootActive, final, after, entryRun, machine, matchedScope, ?_, retired, ?_, ?_, ?_⟩
  · rw [countAfter, sameCount, count]
    exact (CallingCertificate.originalEvaluator_spec).2.1.symm
  · intro slot member
    have outside : slot ∉ [59, 64, 65, 66, 67, 68, 69, 70] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [rootsAfter slot outside]
    exact unboundAll slot (List.mem_append_right [61, 64, 65, 66, 67, 68, 69, 70] member)
  · simpa only [native, numberKey] using rootInspection
  · intro fuel budget fuelBound budgetBound
    obtain ⟨common, setup, head, tail, score, root⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
    exact ⟨common, setup, head, tail, score, root,
      stable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
