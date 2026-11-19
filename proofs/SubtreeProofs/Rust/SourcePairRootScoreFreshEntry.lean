module

public import SubtreeProofs.Rust.SourcePairRootScoreFreshScope
public import SubtreeProofs.Rust.SourcePairScoreFreshEntry
public import SubtreeProofs.Rust.SourcePrefixIdentity

/-! Parsed pair/pair miss entry through all root-score instructions. Native
subtotal success selects this route, while the root-score result still covers
both overflow and contraction. Actual prior prefixes derive count/root support. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_root_score_scope_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads output : MemoTable) (heads tails : CommonEmbedding)
    (subtotal : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
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
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, output))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal) :
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active minimumFuel minimumBudget lookupWorld lookupActive missWorld missActive headWorld headActive tailWorld tailActive scoreWorld scoreActive final after,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      OriginalLoanMachine world callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootScoreScope heads tails output subtotal final after ∧
      after.state 59 = Slot.ofValue (encodeNumberOption ((Aeneas.Std.U32.checked_add subtotal 1#u32).map (fun value => value.val))) ∧
      Derived.scrutinee final after callers (.discriminant (.local 59)) = some (numberKey (checkedAdd32 subtotal.val 1), after) ∧
      LocalOwnersAbove world.memory.length final after 37 ∧ LocalOwnersAbove world.memory.length final after 47 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix entered active lookupWorld lookupActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers missCases missSetupActions lookupWorld lookupActive missWorld missActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers headCases headActions missWorld missActive headWorld headActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers tailCases tailActions headWorld headActive tailWorld tailActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers scoreCases scoreActions tailWorld tailActive scoreWorld scoreActive ∧
        Calling.Prefix (Recursive.original budget fuel) callers rootScoreCases rootScoreActions scoreWorld scoreActive final after := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, entryRun, tailScope, scoreMachine, scoreScope, scoreValue, scoreInspection, headsScore, tailsScore, prefixes⟩ :=
    entry_pair_score_scope_complete_fresh hw hc view lh lt rh rt table afterHeads output heads tails leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess
  obtain ⟨sameWorld, sameActive, sameEntry, _, _, count, unbound, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  obtain ⟨common, setup, head, tail, score⟩ := prefixes minFuel minBudget (by rfl) (by rfl)
  have sameCount : scoreActive.count = active.count :=
    score.shape.2.1.trans (tail.shape.2.1.trans (head.shape.2.1.trans (setup.shape.2.1.trans common.shape.2.1)))
  have unboundRoot : ∀ slot ∈ [55, 58, 59, 60], scoreActive.roots slot = none := by
    intro slot member
    have preserves : ∀ actions ∈ [commonPrefix, missSetupActions, headActions, tailActions, scoreActions],
        ∀ act ∈ actions, keepsRoot slot act := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide +kernel
    rw [score.shape.2.2 slot (preserves scoreActions (by simp)), tail.shape.2.2 slot (preserves tailActions (by simp)),
      head.shape.2.2 slot (preserves headActions (by simp)), setup.shape.2.2 slot (preserves missSetupActions (by simp)),
      common.shape.2.2 slot (preserves commonPrefix (by simp))]
    exact unbound slot (by simp only [List.mem_cons, List.not_mem_nil, or_false] at member
                           rcases member with rfl | rfl | rfl | rfl <;> decide)
  obtain ⟨rootFuel, rootBudget, final, after, machine, rootScope, _, _, _, _, rootInspection, headsRoot, tailsRoot, rootStable⟩ :=
    pair_root_score_scope_complete_fresh scoreMachine scoreScope subtotal subtotalSuccess headsScore tailsScore (by rw [sameCount, count]; decide) unboundRoot
  refine ⟨entered, active, max minFuel rootFuel, max minBudget rootBudget, lookupWorld, lookupActive, missWorld, missActive,
    headWorld, headActive, tailWorld, tailActive, scoreWorld, scoreActive, final, after, entryRun, machine, rootScope, ?_, rootInspection, headsRoot, tailsRoot, ?_⟩
  · rw [← checkedAdd32_native]
    exact rootScope.result
  · intro fuel budget fuelBound budgetBound
    obtain ⟨common, setup, head, tail, score⟩ := prefixes fuel budget ((Nat.le_max_left _ _).trans fuelBound) ((Nat.le_max_left _ _).trans budgetBound)
    exact ⟨common, setup, head, tail, score,
      rootStable fuel budget ((Nat.le_max_right _ _).trans fuelBound) ((Nat.le_max_right _ _).trans budgetBound)⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
