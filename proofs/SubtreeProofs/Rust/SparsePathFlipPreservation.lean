module

public import SubtreeProofs.Rust.SparsePathFlipBounds
import Mathlib.Tactic

/-! # Exact prefix preservation by the actual ranked path-flip writes -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

theorem afterFlip_invariant (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor next : Usize) (failure : Option AssignmentError)
    (h : FlipInvariant dimension assignment parent (assignment root::rest) current column cursor false failure)
    (ht : Assignment.PredecessorTrace assignment parent root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (hPositive : ∀ col ∈ assignment root::rest, 0 < rank col)
    (hNext : next.val = cursor.val+1) :
    let (newCurrent,newColumn,newCursor,newFinished,newFailure) := afterFlip completed predecessor rootIndex column current next
    FlipInvariant dimension assignment parent (assignment root::rest) newCurrent newColumn newCursor newFinished newFailure := by
  obtain ⟨hi,hColumn⟩ := h.active_column rfl
  let vertex : Fin dimension := (assignment root::rest)[cursor.val]
  have hv : column.val = vertex.val := hColumn
  have hPos : 0 < rank vertex := hPositive vertex (List.getElem_mem hi)
  have hPred : predecessor.val[column.val]!.val = (parent vertex).val := by rw [hv]; exact input.predecessor_values vertex hPos
  have hParent : completed.val[predecessor.val[column.val]!.val]!.val = (assignment (parent vertex)).val := by
    rw [hPred]
    exact input.completed_values (parent vertex)
  have hRoot : predecessor.val[column.val]! = rootIndex ↔ parent vertex = root := by
    constructor
    · intro he
      apply Fin.ext
      have hh := congrArg UScalar.val he
      simpa only [hPred,input.root_eq] using hh
    · intro he
      apply UScalar.eq_of_val_eq
      rw [hPred,he,input.root_eq]
  have hAt := ht.at assignment parent root cursor.val hi
  have hLast : parent vertex = root ↔ next.val = (assignment root::rest).length := by
    by_cases hm : cursor.val+1 < (assignment root::rest).length
    · rw [dite_eq_left hm] at hAt
      exact iff_of_false hAt.1 (by omega)
    · rw [dite_eq_right hm] at hAt
      exact iff_of_true hAt (by omega)
  have hValues : ∀ row : Fin dimension, (current.set predecessor.val[column.val]! column).val[row.val]!.val =
      (Assignment.tracePrefixValue assignment (Assignment.augmentTrace assignment (assignment root::rest)) parent (assignment root::rest) next.val row).val := by
    intro row
    rw [hNext]
    exact flip_prefix_set dimension assignment parent root rest ht hn current cursor.val h.length hi h.values
      predecessor.val[column.val]! column hPred hv row
  have hCursor : next.val ≤ (assignment root::rest).length := by omega
  dsimp only [afterFlip]
  by_cases he : predecessor.val[column.val]! = rootIndex
  · have hEnd := hLast.mp (hRoot.mp he)
    simp only [he,↓reduceIte,decide_true]
    refine {
      length := by simpa using h.length
      values := ?_
      cursor_le := hCursor
      column_bound := h.column_bound
      active_column := by intro hh; cases hh
      finished_exact := iff_of_true rfl hEnd
      failure_none := rfl
    }
    simpa only [he] using hValues
  · have hNotEnd : next.val ≠ (assignment root::rest).length := fun hh => he (hRoot.mpr (hLast.mpr hh))
    have hNextLt : next.val < (assignment root::rest).length := by omega
    have hm : cursor.val+1 < (assignment root::rest).length := by omega
    rw [dite_eq_left hm] at hAt
    have hNextColumn : completed.val[predecessor.val[column.val]!.val]!.val = ((assignment root::rest)[next.val]).val := by
      simpa only [hNext,hAt.2] using hParent
    simp only [he,↓reduceIte,decide_false]
    exact {
      length := by simpa using h.length
      values := hValues
      cursor_le := hCursor
      column_bound := by rw [hParent]; exact (assignment (parent vertex)).isLt
      active_column := fun _ => ⟨hNextLt,hNextColumn⟩
      finished_exact := iff_of_false Bool.false_ne_true hNotEnd
      failure_none := rfl
    }

/-- The actual active flip iteration preserves the full prefix invariant and
strictly decreases the number of unprocessed trace columns. -/
theorem flip_body_preserves_spec (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor : Usize) (failure : Option AssignmentError)
    (h : FlipInvariant dimension assignment parent (assignment root::rest) current column cursor false failure)
    (ht : Assignment.PredecessorTrace assignment parent root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (hPositive : ∀ col ∈ assignment root::rest, 0 < rank col) :
    sparse_search.flip_sparse_path_loop.body completed predecessor discovery rootIndex n current column cursor false failure ⦃ result =>
      match result with
      | .done _ => False
      | .cont state => FlipInvariant dimension assignment parent (assignment root::rest) state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2 ∧
          (assignment root::rest).length-state.2.2.1.val < (assignment root::rest).length-cursor.val ⦄ := by
  apply WP.spec_mono (flip_body_from_invariant dimension completed predecessor discovery n rootIndex assignment root parent rank input
    rest current column cursor failure h hn hPositive)
  rintro result ⟨next,hNext,rfl⟩
  refine ⟨afterFlip_invariant dimension completed predecessor discovery n rootIndex assignment root parent rank input rest current column cursor next failure h ht hn hPositive hNext,?_⟩
  obtain ⟨hi,hColumn⟩ := h.active_column rfl
  dsimp only [afterFlip]
  omega

end SubtreeProofs.Rust.SparseSearch

end
