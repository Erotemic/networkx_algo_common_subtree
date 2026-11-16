module

public import SubtreeProofs.Rust.LookupSourceRefinement
public import SubtreeProofs.Rust.Generated.LookupSourceExtraCompare

/-!
The extra comparison is inserted into real temporary Rust source, compiled by
the same Charon release, and reified by the same adapter. This is not a manually
written charged twin. It invalidates the old zero-comparison empty-table budget
while returning exactly the same first-hit answer on that represented input.
-/

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SubtreeProofs.Rust.LookupSource

open verified_ordered_core

theorem extra_compare_execution :
    ∃ cost, run ExtraCompare.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty),
        .reference (encodeWord .Empty)] = some (encodeOption none, cost) ∧
      cost.events = { lookupNodes := 1, compareNodes := 1 } := by
  simp [run, lookup_source_simps, ExtraCompare.body, ExtraCompare.lookup,
    ExtraCompare.compare, encodeTable, encodeWord, encodeOption]

/-- The old bound has t=0 and allows no comparisons; the actual changed source
executes one. Value correctness alone would not reject this mutation. -/
theorem extra_compare_violates_old_bound :
    ∃ cost, run ExtraCompare.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty),
        .reference (encodeWord .Empty)] = some (encodeOption none, cost) ∧
      ¬cost.events.compareNodes ≤ MemoizedOrderedSolver.memoLength .Empty *
        ((2 * (OrderedSolver.toDyck .Empty).semilength + 1) +
          (2 * (OrderedSolver.toDyck .Empty).semilength + 1)) := by
  obtain ⟨cost, he, hc⟩ := extra_compare_execution
  refine ⟨cost, he, ?_⟩
  rw [hc]
  decide

end SubtreeProofs.Rust.LookupSource
