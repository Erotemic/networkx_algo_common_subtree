module

public import SubtreeProofs.Rust.SourcePairMatchedQueryEntry

/-! Retain the matched candidate independently of the current location of the
owned table. Contraction setup moves the table into its recursive argument. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure MatchedCandidateScope (heads tails : CommonEmbedding) (total : Aeneas.Std.U32) (active : Activation) : Prop where
  headHole : active.state 37 = resultWordHole heads.edges
  tailHole : active.state 47 = resultWordHole tails.edges
  totalValue : active.state 58 = .number total.val
  candidate : active.state 64 = Slot.ofValue (encodeResult (matchedWitness heads tails total))
  retired : ∀ slot ∈ [65, 70], active.roots slot = none

theorem MatchedScope.candidate_scope {heads tails : CommonEmbedding} {table : MemoTable} {total : Aeneas.Std.U32} {active : Activation}
    (h : MatchedScope heads tails table total active) : MatchedCandidateScope heads tails total active :=
  ⟨h.headHole, h.tailHole, h.totalValue, h.candidate, h.retired⟩

theorem MatchedCandidateScope.through_prefix {heads tails : CommonEmbedding} {total : Aeneas.Std.U32}
    {callee : Derived.Callees} {callers : List Activation} {suffix : Code} {actions : List Action}
    {world final : World} {active after : Activation} (scope : MatchedCandidateScope heads tails total active)
    (run : Calling.Prefix callee callers suffix actions world active final after)
    (unchanged : ∀ slot ∈ [37, 47, 58, 64], actions.all (LocalPreservation.action slot) = true)
    (roots : ∀ slot ∈ [65, 70], ∀ act ∈ actions, keepsRoot slot act) : MatchedCandidateScope heads tails total after := by
  refine ⟨(run.closed_local_same_calls (index := 37) (by rw [scope.headHole]; exact resultWordHole_typed heads.edges)
      (.adt .embedding) (unchanged _ (by simp))).trans scope.headHole,
    (run.closed_local_same_calls (index := 47) (by rw [scope.tailHole]; exact resultWordHole_typed tails.edges)
      (.adt .embedding) (unchanged _ (by simp))).trans scope.tailHole,
    (run.closed_local_same_calls (index := 58) (by rw [scope.totalValue]; exact .number total.hmax)
      .u32 (unchanged _ (by simp))).trans scope.totalValue,
    (run.closed_local_same_calls (index := 64) (by rw [scope.candidate]; exact ofValue_typed (result_typed (matchedWitness heads tails total)))
      (.adt .embedding) (unchanged _ (by simp))).trans scope.candidate, ?_⟩
  intro slot member
  rw [run.shape.2.2 slot (roots slot member)]
  exact scope.retired slot member

end SubtreeProofs.Rust.SourceEval.Evaluator
