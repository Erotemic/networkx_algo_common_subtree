module

public import SubtreeProofs.Rust.SourcePairFinishCleanup
public import SubtreeProofs.Rust.SourceReturnTotality

/-! The full successful-right finish continuation executes its real cleanup and
checked return. Complete ownership, witness provenance and caller reads survive. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_finish_return_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : FinishPackedScope lh lt rh rt heads tails left right table total active)
    (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot)
    (count : 113 ≤ active.count)
    (above : LocalResultOwnersAbove before.memory.length world active 0)
    (held : ∀ slot ∈ [71, 85], LocalOwnersAbove before.memory.length world active slot) :
    let value := encodeOutput (some (selectedWitness (matchedWitness heads tails total) left right))
      (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)
    ∃ final after cell cost owners,
      Calling.exec callee callers (finishCode 56) world active = some (.returned final after (cell, value), cost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads ∧ after.Valid final ∧
      (∀ caller ∈ callers, caller.Valid final) ∧ final.WellFormed ∧
      Readable final.memory final.live cell value ∧ Footprint final.memory cell owners ∧
      OwnerFrame final (owners ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
      BoxCoverage final (owners ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove before.memory.length final.memory cell ∧ final.memory = world.memory := by
  dsimp only
  obtain ⟨final, current, steps, machine, output, freshOutput, root0, others, countAfter, frameAfter, memory⟩ :=
    pair_finish_cleanup_complete h callee scope older present count above held
  obtain ⟨binding, bound⟩ := root0
  have closed : ClosedState current.state := by
    intro slot
    by_cases isZero : slot = 0
    · subst slot
      exact ⟨_, by rw [output]; exact ofValue_typed (encodeOutput_typed _ _),
        .tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))⟩
    · exact ⟨.u32, by rw [(others slot isZero).2]; exact .empty _, .u32⟩
  have loans := Derived.ReturnLoansAllowed.of_closed_preserved (fun slot _ => closed slot) h.native.previousCallers
    h.native.beforeWellFormed machine.native.kept (machine.native.fresh 0 binding bound)
  obtain ⟨cell, owners, returned, sourceReturn, valid, readable, footprint, ownerFrame, coverage⟩ :=
    Derived.returnValue_total machine.native.valid machine.native.callersValid machine.native.wellFormed machine.native.separate
      machine.native.ownerFrame machine.native.coverage bound (by rw [output]; exact Slot.materialize_ofValue _) loans
  have provenance := Derived.return_result_owner_provenance freshOutput returned
  obtain ⟨cost, whole⟩ := steps.exec returned
  refine ⟨final, {current with state := current.state.set 0 .empty}, cell, cost, owners, whole, ?_,
    machine.native.separate, machine.native.fresh, machine.native.kept, valid, machine.native.callersValid,
    machine.native.wellFormed, readable, footprint, ownerFrame, coverage, provenance, memory⟩
  intro slot
  by_cases isZero : slot = 0
  · subst slot; simp only [Partial.Locals.set, ite_true]
  · simpa only [Partial.Locals.set, isZero, ite_false] using (others slot isZero).2

end SubtreeProofs.Rust.SourceEval.Evaluator
