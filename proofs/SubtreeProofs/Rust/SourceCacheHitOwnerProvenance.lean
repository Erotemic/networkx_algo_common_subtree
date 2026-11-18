module

public import SubtreeProofs.Rust.SourcePrefixOwnerProvenance
public import SubtreeProofs.Rust.SourceCacheHitBody

/-! The complete parsed hit path transfers the lookup helper's bounded owners
through its real payload moves and mixed witness/table result. Old table owners
and legal shared aliases are retained independently. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

private theorem hit_transfer_plan : OwnerTransfer 4 (hitActions.take 10) 10 := by
  refine .keep (by decide) (by decide) ?_
  refine .assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) ?_
  refine .keep (by decide) (by decide) ?_
  refine .keep (by decide) (by decide) ?_
  refine .assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) ?_
  refine .assign (fun _ _ _ above => OperandSourcesAbove.single_move above rfl) ?_
  refine .keep (by decide) (by decide) ?_
  refine .keep (by decide) (by decide) ?_
  refine .keep (by decide) (by decide) ?_
  exact .keep (by decide) (by decide) (.nil 10)

theorem hit_prefix_owner_provenance {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {bound : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (above : LocalOwnersAbove bound world active 4)
    (steps : Calling.Prefix callee callers .done hitActions world active final after) :
    LocalResultOwnersAbove bound final after 0 := by
  have splitSteps : Calling.Prefix callee callers .done ((hitActions.take 10) ++ hitActions.drop 10) world active final after := by
    simpa only [List.take_append_drop] using steps
  obtain ⟨middle, current, first, rest⟩ := splitSteps.split
  have witness := first.owner_transfer hit_transfer_plan ha hc hw above
  obtain ⟨valid, callersValid, wellFormed⟩ := first.noncall_valid ha hc hw (by decide +kernel)
  change Calling.Prefix callee callers .done
    (.assign 0 (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)]) :: hitActions.drop 11)
    middle current final after at rest
  cases rest with
  | @cons _ next _ _ interim _ _ _ cost run tail =>
    let code := (Action.assign 0 (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)]) :: hitActions.drop 11).foldr Control.Tree.step .done
    have prepared := Activation.forgetRefs_valid valid code
    have acted : Derived.assign middle (current.forgetRefs code) callers 0
        (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)]) = some (next, interim) := by
      simp only [Calling.instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨w, a⟩, acted, last⟩ := run
      cases last
      exact acted
    have fresh := Derived.assign_result_owner_provenance prepared
      (OperandSourcesAbove.single_move (witness.prepare_any code) rfl) acted
    have checked := Derived.action_spec prepared callersValid wellFormed
      (.assign 0 (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)])) acted
    exact tail.retirement_result_owner_provenance checked.valid checked.callers checked.wellFormed
      (by intro action member
          simp only [hitActions, List.drop, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals exact ⟨_, by first | exact Or.inl rfl | exact Or.inr rfl⟩)
      (by intro action member
          simp only [hitActions, List.drop, List.mem_cons, List.not_mem_nil, or_false] at member
          rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide) fresh

theorem common_prefix_owner_provenance {before world final : World} {active after : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat} {fuel budget : Nat}
    (h : LoanSafeMachine before callers previous external world active)
    (positive : 0 < fuel) (count : 9 ≤ active.count) (left right : BalancedWord) (table : MemoTable)
    (inputs : InputLocals left right table active.state)
    (unbound : ∀ slot ∈ [0, 4, 5, 6, 7, 8], active.roots slot = none)
    (steps : Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch commonPrefix world active final after) :
    LocalOwnersAbove before.memory.length final after 4 := by
  obtain ⟨middle, current, resultRoot, tableView, leftView, rightView, borrowed, machine, _, _,
    resultBinding, _, _, _, _, _, tableValue, leftValue, rightValue, _⟩ :=
    borrow_prefix_complete h (Recursive.original budget fuel) count left right table inputs unbound
  change Calling.Prefix (Recursive.original budget fuel) callers lookupSwitch
    (borrowPrefix ++ (.call .lookup lookupArgs 4 :: lookupRetire)) world active final after at steps
  obtain ⟨sameWorld, sameActive, first, rest⟩ := steps.split
  have same := borrowed.unique first
  obtain ⟨rfl, rfl⟩ := same
  cases rest with
  | @cons _ returned _ _ result _ _ _ cost run retire =>
    have execute : Derived.call (Recursive.original budget fuel) middle (current.forgetRefs lookupSuffix) callers
        .lookup lookupArgs 4 = some (returned, result, cost) := by
      simp only [Calling.instruction, bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨w, a, work⟩, execute, last⟩ := run
      cases last
      exact execute
    have prepared := machine.prepare lookupSuffix
    have first : (current.forgetRefs lookupSuffix).state 5 = .shared (encodeTable table) := by
      rw [Activation.forgetRefs_observed current lookupSuffix 5 (by decide +kernel)]; exact tableValue
    have second : (current.forgetRefs lookupSuffix).state 7 = .shared (encodeWord left) := by
      rw [Activation.forgetRefs_observed current lookupSuffix 7 (by decide +kernel)]; exact leftValue
    have third : (current.forgetRefs lookupSuffix).state 8 = .shared (encodeWord right) := by
      rw [Activation.forgetRefs_observed current lookupSuffix 8 (by decide +kernel)]; exact rightValue
    have source := lookup_arguments left right table first second third
    have typed : SnapshotFieldsTyped [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)]
        [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] :=
      .cons (.shared (table_typed table)) (.cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) .nil))
    have output : Types.callOutput .lookup [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)] = some (.adt .optional) := by
      simp only [Types.callOutput, reduceCtorEq, ite_false, Types.inputs, SourceTypes.sameList_refl, ite_true, Types.output]
    have ready := Derived.call_ready_from_values (callers := callers) prepared.valid source typed output
    have fresh := Derived.original_helper_call_fresh_output fuel budget positive prepared.valid prepared.callersValid
      prepared.wellFormed (by simp [Helpers.FreshOutputHelper]) ready execute
    have checked := Derived.call_spec (Recursive.original_typed_respects budget fuel) prepared.valid prepared.callersValid
      prepared.wellFormed .lookup lookupArgs 4 ready execute
    have plan : OwnerTransfer 4 lookupRetire 4 :=
      .keep (by decide) (by decide) (.keep (by decide) (by decide) (.keep (by decide) (by decide) (.nil 4)))
    exact retire.owner_transfer plan checked.2.2.2.2.1
      (lookup_call_machine budget fuel machine left right table resultBinding tableValue leftValue rightValue execute).callersValid
      checked.2.2.2.2.2.2.1 (fresh.weaken machine.memoryBound)

theorem returnResult_owner_provenance {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {bound : Nat} {packet : ValueCell} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (above : LocalResultOwnersAbove bound world active 0)
    (run : Calling.exec callee callers returnResult world active = some (.returned final after packet, cost)) :
    ResultOwnersAbove bound final.memory packet.1 := by
  let actions : List Action := [.drop 3, .storageDead 3, .storageDead 2, .storageDead 1]
  change Calling.exec callee callers (actions.foldr Control.Tree.step .ret) world active = _ at run
  obtain ⟨middle, current, last, steps, returned⟩ := Calling.prefix_of_exec run
  have fresh := steps.retirement_result_owner_provenance ha hc hw
    (by intro action member
        simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl
        all_goals exact ⟨_, by first | exact Or.inl rfl | exact Or.inr rfl⟩)
    (by intro action member
        simp only [actions, List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl <;> decide) above
  exact Derived.return_result_owner_provenance fresh returned

theorem hit_continuation_owner_provenance {before world final : World} {active initial after : Activation}
    {callers : List Activation} {previous : Resources} {external : List Nat} {bound : Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 13 ≤ active.count)
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result)
    (above : LocalOwnersAbove bound world active 4) {packet : ValueCell} {cost : Cost}
    (run : Calling.exec callee callers lookupSwitch world active = some (.returned final after packet, cost)) :
    ResultOwnersAbove bound final.memory packet.1 := by
  obtain ⟨middle, current, steps, machine, _⟩ := hit_branch_complete h callee scope unbound count result hit
  have fresh := hit_prefix_owner_provenance h.native.valid h.native.callersValid h.native.wellFormed above steps
  obtain ⟨branchCost, branchRun⟩ := steps.exec (Calling.exec_done callee callers middle current)
  have branch : Calling.exec callee callers cacheHit world active = some (.next middle current, branchCost) := by
    rw [cacheHit_actions]; exact branchRun
  have observed := (lookup_switch_native h.native left right table scope).1
  rw [hit] at observed
  rw [lookupSwitch, Calling.exec_switch, observed] at run
  simp only [lookupKey, Control.selectSource, Control.selectIndex, ite_true, branch, bind, Option.bind] at run
  change (do
    let (actual, last) ← Calling.exec callee callers returnResult middle current
    some (actual, ((Cost.local (1 + (Scrutinee.discriminant (.local 4)).weight)).plus branchCost).plus last)) = _ at run
  simp only [bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨actual, last⟩, returned, ending⟩ := run
  have same := (Prod.mk.inj (Option.some.inj ending)).1
  change actual = .returned final after packet at same
  subst actual
  exact returnResult_owner_provenance machine.native.valid machine.native.callersValid machine.native.wellFormed fresh returned

theorem entry_hit_body_complete_fresh {world : World} {callers : List Activation} {previous : Resources}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result) :
    let packets := inputPackets leftCell rightCell tableCell left right table
    ∃ entered active fuel budget final after cell cost,
      enter world world.memory.length CallingCertificate.originalEvaluator.source.localCount packets = some (entered, active) ∧
      LoanSafeMachine world callers previous external entered active ∧
      active.state = initialState [.reference (encodeWord left), .reference (encodeWord right), encodeTable table] ∧
      Calling.exec (Recursive.original budget fuel) callers body entered active =
        some (.returned final after (cell, encodeOutput (some result) table), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → world.memory.length ≤ binding.address) ∧
      Preserves world final previous.reads ∧ ResultOwnersAbove world.memory.length final.memory cell := by
  dsimp only
  obtain ⟨entered, active, fuel, budget, middle, current, entryRun, state, count, unbound,
    machine, scope, origins, switchRun, steps⟩ :=
    entry_common_prefix_complete hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  obtain ⟨sameWorld, sameActive, sameEntry, initialMachine, _, _, _, _⟩ :=
    native_entry_machine hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead input frame covered
  have same := Prod.mk.inj (Option.some.inj (entryRun.symm.trans sameEntry))
  obtain ⟨rfl, rfl⟩ := same
  have firstSteps := steps (fuel + 1) budget (by omega) (by rfl)
  have fresh := common_prefix_owner_provenance initialMachine (by omega) (by rw [count]; decide +kernel)
    left right table (by rw [state]; exact initial_inputs left right table)
    (by intro slot member
        apply unbound
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel) firstSteps
  have currentCount : 13 ≤ current.count := by rw [scope.count, count]; decide
  have query := scope.query_machine machine origins unbound
  obtain ⟨final, after, cell, last, continuation, empty, separate, freshRoots, kept⟩ :=
    hit_continuation_complete query (Recursive.original budget (fuel + 1)) scope unbound currentCount result hit
  have resultFresh := hit_continuation_owner_provenance query (Recursive.original budget (fuel + 1))
    scope unbound currentCount result hit fresh continuation
  obtain ⟨cost, whole⟩ := firstSteps.exec continuation
  have bodyRun : Calling.exec (Recursive.original budget (fuel + 1)) callers body entered active =
      some (.returned final after (cell, encodeOutput (some result) table), cost) := by
    rw [← actual_body, actual_body_common_prefix]; exact whole
  exact ⟨entered, active, fuel + 1, budget, final, after, cell, cost, entryRun, initialMachine, state,
    bodyRun, empty, separate, freshRoots, kept, resultFresh⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
