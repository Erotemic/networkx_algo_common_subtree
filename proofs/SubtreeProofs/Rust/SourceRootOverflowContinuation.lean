module

public import SubtreeProofs.Rust.SourceRootOverflowContext
public import SubtreeProofs.Rust.SourcePairFailureOuterReturn

/-! Execute root overflow, total-payload retirement, both owned witness drops,
all outer cleanup joins and the guarded parameter return. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem root_overflow_continuation_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootScoreScope heads tails table subtotal world active) (storage : EmptyRootStorage world active 0)
    (present : rootPresence active.roots = fun slot => pairRootScoreLiveRoots.contains slot) (count : 113 ≤ active.count)
    (older : PairOlderMasks active)
    (headsFresh : LocalOwnersAbove before.memory.length world active 37)
    (tailsFresh : LocalOwnersAbove before.memory.length world active 47)
    (overflow : checkedAdd32 subtotal.val 1 = none)
    (inspection : Derived.scrutinee world active callers (.discriminant (.local 59)) =
      some (numberKey (checkedAdd32 subtotal.val 1), active)) :
    ∃ scoreWorld scoreActive scoreCost tailWorld tailActive tailCost headWorld headActive headCost
      joinWorld joinActive joinCost final after cell returnCost,
      Calling.exec callee callers rootScoreCases world active = some (.next scoreWorld scoreActive, scoreCost) ∧
      Calling.exec callee callers cleanupTails scoreWorld scoreActive = some (.next tailWorld tailActive, tailCost) ∧
      Calling.exec callee callers cleanupHeads tailWorld tailActive = some (.next headWorld headActive, headCost) ∧
      Calling.exec callee callers cleanupInputs headWorld headActive = some (.next joinWorld joinActive, joinCost) ∧
      Calling.exec callee callers returnResult joinWorld joinActive = some (.returned final after (cell, encodeOutput none table), returnCost) ∧
      (∀ slot, after.state slot = .empty) ∧ after.RootsSeparate callers ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      Preserves before final previous.reads := by
  obtain ⟨packed, packetActive, packing, packedMachine, packedPresence, output0, empty42, packedCount⟩ :=
    root_overflow_pack_complete h callee scope storage present count
  have masksP := older.through_prefix packing (by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl <;> decide +kernel)
  have headsP := packing.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed headsFresh
  have tailsP := packing.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by decide +kernel))
    h.native.valid h.native.callersValid h.native.wellFormed tailsFresh
  obtain ⟨scoreWorld, scoreActive, subtotalCost, tailWorld, tailActive, tailCost, headWorld, headActive, headCost,
    joinWorld, joinActive, joinCost, final, after, cell, returnCost, subtotalWhole, cleanupTailsRun, cleanupHeadsRun,
    cleanupInputsRun, returned, empty, separate, fresh, kept⟩ :=
    pair_failure_outer_return_complete packedMachine callee packedPresence (by omega) masksP empty42
      (by rw [packing.boxes_same_calls (by decide +kernel), scope.totalEmpty]; simp only [Slot.dropWork])
      headsP tailsP output0
  obtain ⟨packCost, packRun⟩ := packing.exec (Calling.exec_done callee callers packed packetActive)
  have overflowRun : Calling.exec callee callers rootOverflow world active = some (.next packed packetActive, packCost) := by
    rw [rootOverflow_actions]; exact packRun
  have rootRun : Calling.exec callee callers rootScoreCases world active = some (.next scoreWorld scoreActive,
      ((Cost.local (1 + (Scrutinee.discriminant (.local 59)).weight)).plus packCost).plus subtotalCost) := by
    rw [rootScoreCases, Calling.exec_switch, inspection, overflow]
    simp only [numberKey, Control.selectSource, Control.selectIndex, ite_true, overflowRun, bind, Option.bind]
    rw [subtotalWhole]
  exact ⟨scoreWorld, scoreActive, _, tailWorld, tailActive, tailCost, headWorld, headActive, headCost, joinWorld, joinActive, joinCost,
    final, after, cell, returnCost, rootRun, cleanupTailsRun, cleanupHeadsRun, cleanupInputsRun, returned, empty, separate, fresh, kept⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
