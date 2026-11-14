module

public import SubtreeProofs.Rust.SparsePathFlipInvariant
import Mathlib.Tactic

/-! # Deriving the actual flip loop's local bounds from its ranked trace -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

/-- The full source flip invariant and ranked trace discharge every local
array/counter/rank premise of the actual iteration. -/
theorem flip_local_bounds (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor : Usize) (failure : Option AssignmentError)
    (h : FlipInvariant dimension assignment parent (assignment root::rest) current column cursor false failure)
    (hn : (assignment root::rest).Nodup) (hPositive : ∀ col ∈ assignment root::rest, 0 < rank col) :
    cursor.val < n.val ∧ column.val < n.val ∧ predecessor.val[column.val]!.val < n.val ∧
      0 < discovery.val[column.val]!.val ∧
      (predecessor.val[column.val]! ≠ rootIndex →
        completed.val[predecessor.val[column.val]!.val]!.val < n.val ∧
        0 < discovery.val[completed.val[predecessor.val[column.val]!.val]!.val]!.val ∧
        discovery.val[completed.val[predecessor.val[column.val]!.val]!.val]!.val < discovery.val[column.val]!.val) := by
  obtain ⟨hi,hColumn⟩ := h.active_column rfl
  let vertex : Fin dimension := (assignment root::rest)[cursor.val]
  have hVertex : vertex ∈ assignment root::rest := List.getElem_mem hi
  have hv : column.val = vertex.val := hColumn
  have hRank := hPositive vertex hVertex
  have hPred : predecessor.val[column.val]!.val = (parent vertex).val := by
    rw [hv]
    exact input.predecessor_values vertex hRank
  have hDisc : discovery.val[column.val]!.val = rank vertex := by
    rw [hv]
    exact input.discovery_values vertex
  have hLength : (assignment root::rest).length ≤ dimension := by
    simpa only [Fintype.card_fin] using hn.length_le_card
  refine ⟨by have he := input.dimension_eq; omega,by have he := input.dimension_eq; have hb := h.column_bound; omega,
    ?_,by rw [hDisc]; exact hRank,?_⟩
  · rw [hPred,input.dimension_eq]
    exact (parent vertex).isLt
  · intro hNonroot
    have hNot : parent vertex ≠ root := by
      intro he
      apply hNonroot
      apply UScalar.eq_of_val_eq
      rw [hPred,he,input.root_eq]
    obtain ⟨hParentPositive,hParentLess⟩ := (input.ranked vertex hRank).resolve_left hNot
    have hParentValue : completed.val[predecessor.val[column.val]!.val]!.val = (assignment (parent vertex)).val := by
      rw [hPred]
      exact input.completed_values (parent vertex)
    refine ⟨?_,?_,?_⟩
    · rw [hParentValue,input.dimension_eq]
      exact (assignment (parent vertex)).isLt
    · rw [hParentValue,input.discovery_values]
      exact hParentPositive
    · rw [hParentValue,input.discovery_values,hDisc]
      exact hParentLess

/-- The actual active flip body has no failing branch under the complete
independent state. Every local premise is derived above. -/
theorem flip_body_from_invariant (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor : Usize) (failure : Option AssignmentError)
    (h : FlipInvariant dimension assignment parent (assignment root::rest) current column cursor false failure)
    (hn : (assignment root::rest).Nodup) (hPositive : ∀ col ∈ assignment root::rest, 0 < rank col) :
    sparse_search.flip_sparse_path_loop.body completed predecessor discovery rootIndex n current column cursor false failure ⦃ result => ∃ next,
      next.val = cursor.val+1 ∧ result = .cont (afterFlip completed predecessor rootIndex column current next) ⦄ := by
  have hb := flip_local_bounds dimension completed predecessor discovery n rootIndex assignment root parent rank input rest current column cursor failure h hn hPositive
  have hf := h.failure_none
  subst failure
  exact flip_body_step_spec completed predecessor discovery rootIndex n column cursor current hb.1 hb.2.1
    (input.completed_length.trans input.dimension_eq.symm) (input.predecessor_length.trans input.dimension_eq.symm)
    (input.discovery_length.trans input.dimension_eq.symm) (h.length.trans input.dimension_eq.symm) hb.2.2.1 hb.2.2.2.1 hb.2.2.2.2

end SubtreeProofs.Rust.SparseSearch

end
