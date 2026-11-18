module

public import SubtreeProofs.Rust.SourcePairFinishComplete
public import SubtreeProofs.Rust.SourceCloseTotality

/-! Construct checked call-frame closure after the successful-right finish.
Complete output ownership and original caller guards supply the escape checks;
no successful close or expected final world is an input. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_finish_closed_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external guards : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    {lh lt rh rt : BalancedWord} {heads tails left right : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32}
    (scope : PairRightScope lh lt rh rt heads tails left total (some right) table world active)
    (above : LocalOwnersAbove before.memory.length world active 88)
    (held : ∀ slot ∈ [64, 71, 81, 85], LocalOwnersAbove before.memory.length world active slot)
    (storage : EmptyRootStorage world active 0) (older : PairOlderMasks active)
    (present : rootPresence active.roots = fun slot => pairRightLiveRoots.contains slot)
    (count : 113 ≤ active.count)
    (unbound : ∀ slot ∈ [96, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112], active.roots slot = none)
    (protectedReads : guards ⊆ previous.reads) :
    let value := encodeOutput (some (selectedWitness (matchedWitness heads tails total) left right))
      (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)
    ∃ minimumFuel minimumBudget middle after final cell cost,
      close middle after callers guards (cell, value) = some final ∧
      (∀ slot, after.state slot = .empty) ∧
      final.WellFormed ∧ Readable final.memory final.live cell value ∧ Preserves before final guards ∧
      (∀ slot binding, after.roots slot = some binding → final.live binding.address = false) ∧
      (∃ owners, Footprint final.memory cell owners ∧
        OwnerFrame final (owners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (owners ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove before.memory.length final.memory cell ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.exec (Recursive.original budget fuel) callers finish world active = some (.returned middle after (cell, value), cost) := by
  dsimp only
  obtain ⟨minimumFuel, minimumBudget, middle, after, cell, cost, empty, separate, fresh, kept, valid,
    callersValid, wellFormed, readable, owners, resultFresh, stable⟩ :=
    pair_finish_complete h scope above held storage older present count unbound
  obtain ⟨outputOwners, footprint, ownerFrame, covered⟩ := owners
  obtain ⟨final, closeRun, memory, _, finalWf, finalRead, closeKept, retired, finalFootprint, finalFrame, finalCoverage⟩ :=
    close_total (guards := guards)
      (packet := (cell, encodeOutput (some (selectedWitness (matchedWitness heads tails total) left right))
        (.Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) left right⟩ table)))
      valid callersValid wellFormed separate
      (fun slot => by rw [empty slot]; simp only [Slot.dropWork]) readable (encodeOutput_typed _ _)
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) footprint ownerFrame covered
      (by intro suspended current; rw [current.unique (h.native.previousCallers.transport kept)]; exact protectedReads)
      (by intro slot binding bound suspended current borrowed
          have old := h.native.previousCallers.preserved_read_bound h.native.beforeWellFormed kept current binding.address
            (current.loans_subset_reads borrowed)
          have new := fresh slot binding bound
          omega)
  exact ⟨minimumFuel, minimumBudget, middle, after, final, cell, cost, closeRun, empty, finalWf, finalRead,
    (kept.weaken protectedReads).trans closeKept, retired, ⟨outputOwners, finalFootprint, finalFrame, finalCoverage⟩,
    (by rw [memory]; exact resultFresh), stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
