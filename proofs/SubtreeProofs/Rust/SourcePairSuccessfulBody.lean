module

public import SubtreeProofs.Rust.SourcePairSuccessfulRouting
public import SubtreeProofs.Rust.SourcePairFinishClosure
public import SubtreeProofs.Rust.SourcePairRightStorageEntry

/-! Construct the actual successful pair/pair parent body from parsed entry,
four smaller fresh contracts and independent native success equations. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem entry_pair_successful_body_complete {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (lh lt rh rt : BalancedWord) (table afterHeads afterTails : MemoTable) (heads tails : CommonEmbedding)
    (subtotal total : Aeneas.Std.U32) (leftCell rightCell tableCell : Cell)
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
    (tailSuccess : memoized_common_embedding lt rt afterHeads = .ok (some tails, afterTails))
    (subtotalSuccess : Aeneas.Std.U32.checked_add heads.edges tails.edges = some subtotal)
    (rootSuccess : Aeneas.Std.U32.checked_add subtotal 1#u32 = some total)
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (left : CommonEmbedding) (afterLeft : MemoTable)
    (leftSuccess : memoized_common_embedding (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails = .ok (some left, afterLeft))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt))
    (right : CommonEmbedding) (afterRight : MemoTable)
    (rightSuccess : memoized_common_embedding (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft = .ok (some right, afterRight)) :
    let result := selectedWitness (matchedWitness heads tails total) left right
    let output := MemoTable.Entry ⟨.Pair lh lt, .Pair rh rt, result⟩ afterRight
    let packets := inputPackets leftCell rightCell tableCell (.Pair lh lt) (.Pair rh rt) table
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput (some result) output), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads ∧ ResultOwnersAbove world.memory.length final.memory cell := by
  dsimp only
  obtain ⟨entered, active, minFuel, minBudget, lookupWorld, lookupActive, missWorld, missActive, headWorld, headActive,
    tailWorld, tailActive, scoreWorld, scoreActive, rootWorld, rootActive, matchedWorld, matchedActive, concatWorld, concatActive,
    viewsWorld, viewsActive, argumentWorld, argumentActive, callWorld, callActive, leftWorld, leftActive, rightConcatWorld, rightConcatActive,
    rightViewsWorld, rightViewsActive, rightArgumentWorld, rightArgumentActive, rightCallWorld, rightCallActive, rightWorld, rightActive,
    found, output, _, _, _, _, entryRun, machine, scope, leftInspection, native, rightInspection, count, future,
    _, _, freshResult, held, storage, _, stable⟩ :=
    entry_pair_right_scope_storage_complete_provenance hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
      leftCell rightCell tableCell leftRead rightRead tableRead input frame covered miss headsTotal tailsTotal headSuccess tailSuccess
      subtotalSuccess rootSuccess leftTotal left afterLeft leftSuccess rightTotal
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans rightSuccess))
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, initialStateEq, _, _, _⟩ :=
    native_entry_machine hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  have inputTypes : SnapshotFieldsTyped [.reference (encodeWord (.Pair lh lt)), .reference (encodeWord (.Pair rh rt)), encodeTable table]
      (Types.inputs CallingCertificate.originalEvaluator.source.function) := by
    rw [CallingCertificate.originalEvaluator_spec.1]
    exact .cons (.shared (word_typed _)) (.cons (.shared (word_typed _)) (.cons (table_typed _) .nil))
  have typed : LocalsTyped CallingCertificate.originalEvaluator.locals active.state := by
    rw [initialStateEq]
    exact Types.initial_typed inputTypes CallingCertificate.originalEvaluator.boundary
  obtain ⟨common0, setup0, head0, tail0, score0, root0, _, _, _, _, _, _, _, left0, _, _, _, _, _, _, right0⟩ :=
    stable minFuel minBudget (by rfl) (by rfl)
  have older := pair_right_older_masks minFuel minBudget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
    common0 setup0 head0 tail0 score0 root0 left0 right0
  have present := pair_right_root_presence minFuel minBudget entryRun (by simp [inputPackets]) common0 setup0 head0 tail0 score0 root0 left0 right0
  obtain ⟨finishFuel, finishBudget, final, after, cell, finishCost, empty, separate, fresh, kept, _, _, _, _, _, resultFresh, finishStable⟩ :=
    pair_finish_complete machine scope freshResult held storage older present
      (by rw [count, CallingCertificate.originalEvaluator_spec.2.1])
      (by intro slot member
          have high : 96 ≤ slot := by simp only [List.mem_cons, List.not_mem_nil, or_false] at member; omega
          exact future slot high)
  obtain ⟨setupEntered, setupActive, setupFuel, setupBudget, lookupWorld2, lookupActive2, missWorld2, missActive2, setupEntry, _,
    _, _, _, _, _, _, lookupInspection, leftWordInspection, rightWordInspection, setupStable⟩ :=
    entry_miss_setup_complete hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered miss
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj (entryRun.symm.trans setupEntry))
  let fuel := max (max minFuel setupFuel) finishFuel
  let budget := max (max minBudget setupBudget) finishBudget
  have oldFuel : minFuel ≤ fuel := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  have oldBudget : minBudget ≤ budget := (Nat.le_max_left _ _).trans (Nat.le_max_left _ _)
  have earlyFuel : setupFuel ≤ fuel := (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  have earlyBudget : setupBudget ≤ budget := (Nat.le_max_right _ _).trans (Nat.le_max_left _ _)
  obtain ⟨common, setup, head, tail, score, root, _, _, _, _, _, _, _, leftWhole, _, _, _, _, _, _, rightWhole⟩ :=
    stable fuel budget oldFuel oldBudget
  obtain ⟨earlyCommon, earlySetup⟩ := setupStable fuel budget earlyFuel earlyBudget
  obtain ⟨rfl, rfl⟩ := common.unique earlyCommon
  obtain ⟨rfl, rfl⟩ := setup.unique earlySetup
  obtain ⟨headInspection, tailInspection, scoreInspection, rootInspection⟩ :=
    pair_successful_route_inspections fuel budget initialMachine.valid initialMachine.callersValid initialMachine.wellFormed typed
      common setup head tail score root leftWhole
  obtain ⟨cost, whole⟩ := pair_successful_body_routing (Recursive.original budget fuel) common setup head tail score root leftWhole rightWhole
    lookupInspection leftWordInspection rightWordInspection headInspection tailInspection scoreInspection rootInspection leftInspection
    rightInspection (finishStable fuel budget (Nat.le_max_right _ _) (Nat.le_max_right _ _))
  exact ⟨entered, active, fuel, budget, final, after, cell, cost, entryRun, initialMachine, initialStateEq, whole,
    empty, separate, fresh, kept, resultFresh⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
