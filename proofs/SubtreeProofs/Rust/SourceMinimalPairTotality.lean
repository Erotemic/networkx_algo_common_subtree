module

public import SubtreeProofs.Rust.SourcePairSuccessfulTotality
public import SubtreeProofs.Rust.SourceSubtotalOverflowTotality
public import SubtreeProofs.Rust.SourceRootOverflowTotality

/-! A universal fresh contract for the one-edge pair, used as a smaller
recursive premise by concrete contraction-failure consumers. Larger pair/pair
requests still require the full induction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_request_some (left right : BalancedWord) (table : MemoTable)
    (empty : left = .Empty ∨ right = .Empty) :
    ∃ witness output, memoized_common_embedding left right table = .ok (some witness, output) := by
  cases found : MemoizedOrderedSolver.findResult table left right with
  | some result => exact ⟨result, table, cache_hit_native table left right result found⟩
  | none => exact ⟨emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table, empty_native table left right empty found⟩

theorem native_minimal_pair_total_fresh : NativeTotalFresh (.Pair .Empty .Empty) (.Pair .Empty .Empty) := by
  intro world callers previous guards hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead
    owners external input frame coverage protectedReads
  cases found : MemoizedOrderedSolver.findResult table (.Pair .Empty .Empty) (.Pair .Empty .Empty) with
  | some witness =>
    obtain ⟨fuel, budget, final, packet, lookupCost, value, _, native, readable, wf, kept, resources, fresh, stable⟩ :=
      cache_hit_total_fresh hw hc view (.Pair .Empty .Empty) (.Pair .Empty .Empty) table leftCell rightCell tableCell
        leftRead rightRead tableRead input frame coverage protectedReads witness found
    exact ⟨fuel, budget, final, packet, some witness, table, hitRunCost lookupCost,
      value, native, readable, wf, kept, resources, fresh, stable⟩
  | none =>
    obtain ⟨heads, afterHeads, headSuccess⟩ := empty_request_some .Empty .Empty table (Or.inl rfl)
    obtain ⟨tails, afterTails, tailSuccess⟩ := empty_request_some .Empty .Empty afterHeads (Or.inl rfl)
    have base : NativeTotalFresh .Empty .Empty := native_empty_total_fresh .Empty .Empty (Or.inl rfl)
    cases subtotalEq : Aeneas.Std.U32.checked_add heads.edges tails.edges with
    | none =>
      obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, _, fresh, stable⟩ :=
        subtotal_overflow_total_fresh hw hc view .Empty .Empty .Empty .Empty table afterHeads afterTails heads tails
          leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found base base
          headSuccess tailSuccess subtotalEq
      exact ⟨fuel, budget, final, packet, none, afterTails, cost, value,
        subtotal_overflow_native table afterHeads afterTails .Empty .Empty .Empty .Empty heads tails found headSuccess tailSuccess subtotalEq,
        readable, wf, kept, resources, fresh, stable⟩
    | some subtotal =>
      cases rootEq : Aeneas.Std.U32.checked_add subtotal 1#u32 with
      | none =>
        obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, _, fresh, stable⟩ :=
          root_overflow_total_fresh hw hc view .Empty .Empty .Empty .Empty table afterHeads afterTails heads tails subtotal
            leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found base base
            headSuccess tailSuccess subtotalEq rootEq
        exact ⟨fuel, budget, final, packet, none, afterTails, cost, value,
          root_overflow_native table afterHeads afterTails .Empty .Empty .Empty .Empty heads tails subtotal found headSuccess tailSuccess subtotalEq rootEq,
          readable, wf, kept, resources, fresh, stable⟩
      | some total =>
        obtain ⟨left, afterLeft, leftSuccess⟩ := empty_request_some .Empty (.Pair .Empty .Empty) afterTails (Or.inl rfl)
        obtain ⟨right, afterRight, rightSuccess⟩ := empty_request_some (.Pair .Empty .Empty) .Empty afterLeft (Or.inr rfl)
        obtain ⟨fuel, budget, final, packet, cost, value, native, readable, wf, kept, resources, _, fresh, stable⟩ :=
          pair_successful_total_fresh hw hc view .Empty .Empty .Empty .Empty table afterHeads afterTails heads tails subtotal total
            leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found base base
            headSuccess tailSuccess subtotalEq rootEq
            (native_empty_total_fresh .Empty (.Pair .Empty .Empty) (Or.inl rfl)) left afterLeft leftSuccess
            (native_empty_total_fresh (.Pair .Empty .Empty) .Empty (Or.inr rfl)) right afterRight rightSuccess
        exact ⟨fuel, budget, final, packet, some (selectedWitness (matchedWitness heads tails total) left right),
          .Entry ⟨.Pair .Empty .Empty, .Pair .Empty .Empty, selectedWitness (matchedWitness heads tails total) left right⟩ afterRight,
          cost, value, native, readable, wf, kept, resources, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
