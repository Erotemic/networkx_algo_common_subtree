module

public import SubtreeProofs.Rust.SourcePairMatchedEntry
public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Exact original query snapshots, tuple and boxed-child views survive every
constructed tail/score/matched prefix, including their actual calls. Heap graph
validity and original loan bounds remain the independent machine invariants. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def pairQuerySlots : List Nat := [1, 2, 13, 27, 28, 29, 30]
def pairSharedQuerySlots : List Nat := [1, 2, 27, 28, 29, 30]

structure PairQueryScope (lh lt rh rt : BalancedWord) (active : Activation) : Prop where
  left : active.state 1 = .shared (encodeWord (.Pair lh lt))
  right : active.state 2 = .shared (encodeWord (.Pair rh rt))
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  leftHead : active.state 27 = .shared (.boxed (encodeWord lh))
  leftTail : active.state 28 = .shared (.boxed (encodeWord lt))
  rightHead : active.state 29 = .shared (.boxed (encodeWord rh))
  rightTail : active.state 30 = .shared (.boxed (encodeWord rt))

theorem PairHeadScope.query_scope {initial active : Activation} {lh lt rh rt : BalancedWord}
    {result : Option CommonEmbedding} {table : MemoTable} {world : World}
    (h : PairHeadScope initial lh lt rh rt result table world active) : PairQueryScope lh lt rh rt active :=
  ⟨h.left, h.right, h.tuple, h.leftHead, h.leftTail, h.rightHead, h.rightTail⟩

theorem PairTailScope.query_scope {initial active : Activation} {lh lt rh rt : BalancedWord} {heads : CommonEmbedding}
    {result : Option CommonEmbedding} {table : MemoTable} {world : World}
    (h : PairTailScope initial lh lt rh rt heads result table world active) : PairQueryScope lh lt rh rt active :=
  ⟨h.left, h.right, h.tuple, h.leftHead, h.leftTail, h.rightHead, h.rightTail⟩

theorem prefix_pair_queries_complete {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation} {lh lt rh rt : BalancedWord}
    (run : Calling.Prefix callee callers suffix actions world active final after) (scope : PairQueryScope lh lt rh rt active)
    (observed : ∀ slot ∈ pairSharedQuerySlots, LoanEnding.endsBeforeObservation slot suffix = false)
    (unchanged : ∀ slot ∈ pairQuerySlots, actions.all (LocalPreservation.action slot) = true) : PairQueryScope lh lt rh rt after := by
  have same : ∀ slot ∈ pairSharedQuerySlots, after.state slot = active.state slot := by
    intro slot member
    exact run.retained_local_same_calls (observed slot member) (unchanged slot (by
      simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
      simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false]; tauto))
  have tupleSame := run.unshared_local_same_calls (index := 13)
    (by rw [scope.tuple]; intro value impossible; cases impossible) (unchanged 13 (by simp [pairQuerySlots]))
  exact ⟨(same 1 (by simp [pairSharedQuerySlots])).trans scope.left, (same 2 (by simp [pairSharedQuerySlots])).trans scope.right,
    tupleSame.trans scope.tuple, (same 27 (by simp [pairSharedQuerySlots])).trans scope.leftHead,
    (same 28 (by simp [pairSharedQuerySlots])).trans scope.leftTail, (same 29 (by simp [pairSharedQuerySlots])).trans scope.rightHead,
    (same 30 (by simp [pairSharedQuerySlots])).trans scope.rightTail⟩

theorem PairQueryScope.through_tail {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {lh lt rh rt : BalancedWord}
    (h : PairQueryScope lh lt rh rt active)
    (run : Calling.Prefix callee callers tailCases tailActions world active final after) : PairQueryScope lh lt rh rt after := by
  apply prefix_pair_queries_complete run h
  · intro slot member
    simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro slot member
    simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem PairQueryScope.through_score {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {lh lt rh rt : BalancedWord}
    (h : PairQueryScope lh lt rh rt active)
    (run : Calling.Prefix callee callers scoreCases scoreActions world active final after) : PairQueryScope lh lt rh rt after := by
  apply prefix_pair_queries_complete run h
  · intro slot member
    simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro slot member
    simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem PairQueryScope.through_root_score {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {lh lt rh rt : BalancedWord}
    (h : PairQueryScope lh lt rh rt active)
    (run : Calling.Prefix callee callers rootScoreCases rootScoreActions world active final after) : PairQueryScope lh lt rh rt after := by
  apply prefix_pair_queries_complete run h
  · intro slot member
    simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro slot member
    simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem PairQueryScope.through_matched {callee : Derived.Callees} {callers : List Activation}
    {world final : World} {active after : Activation} {lh lt rh rt : BalancedWord}
    (h : PairQueryScope lh lt rh rt active)
    (run : Calling.Prefix callee callers (matchedCode 30) (matchedActions.take 30) world active final after) : PairQueryScope lh lt rh rt after := by
  apply prefix_pair_queries_complete run h
  · intro slot member
    simp only [pairSharedQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel
  · intro slot member
    simp only [pairQuerySlots, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

end SubtreeProofs.Rust.SourceEval.Evaluator
