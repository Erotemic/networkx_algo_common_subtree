module

public import SubtreeProofs.Rust.SparsePathCertificate
public import SubtreeProofs.Rust.SparsePathFlipBody
public import SubtreeProofs.Shared.AssignmentTracePrefix
import Mathlib.Tactic

/-! # Exact prefix invariant for the source ranked path flip -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open AssignmentScanInvariant

structure FlipInput (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat) : Prop where
  dimension_eq : n.val = dimension
  completed_length : completed.length = dimension
  predecessor_length : predecessor.length = dimension
  discovery_length : discovery.length = dimension
  root_eq : rootIndex.val = root.val
  completed_values : ∀ row : Fin dimension, completed.val[row.val]!.val = (assignment row).val
  predecessor_values : ∀ column : Fin dimension, 0 < rank column → predecessor.val[column.val]!.val = (parent column).val
  discovery_values : ∀ column : Fin dimension, discovery.val[column.val]!.val = rank column
  ranked : ∀ column, 0 < rank column → parent column = root ∨
    0 < rank (assignment (parent column)) ∧ rank (assignment (parent column)) < rank column

structure FlipInvariant (dimension : Nat) (assignment : Equiv.Perm (Fin dimension)) (parent : Fin dimension → Fin dimension)
    (path : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor : Usize) (finished : Bool) (failure : Option AssignmentError) : Prop where
  length : current.length = dimension
  values : ∀ row : Fin dimension, current.val[row.val]!.val =
    (Assignment.tracePrefixValue assignment (Assignment.augmentTrace assignment path) parent path cursor.val row).val
  cursor_le : cursor.val ≤ path.length
  column_bound : column.val < dimension
  active_column : finished = false → ∃ hi : cursor.val < path.length, column.val = (path[cursor.val]).val
  finished_exact : finished = true ↔ cursor.val = path.length
  failure_none : failure = none

/-- The exact source vector write extends the independent final-value prefix
by the next predecessor row, with no change to other original coordinates. -/
theorem flip_prefix_set (dimension : Nat) (assignment : Equiv.Perm (Fin dimension)) (parent : Fin dimension → Fin dimension)
    (root : Fin dimension) (rest : List (Fin dimension))
    (ht : Assignment.PredecessorTrace assignment parent root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (current : alloc.vec.Vec Usize) (cursor : Nat)
    (hl : current.length = dimension) (hi : cursor < (assignment root::rest).length)
    (hValues : ∀ row : Fin dimension, current.val[row.val]!.val =
      (Assignment.tracePrefixValue assignment (Assignment.augmentTrace assignment (assignment root::rest)) parent (assignment root::rest) cursor row).val)
    (rowIndex columnIndex : Usize) (hr : rowIndex.val = (parent (assignment root::rest)[cursor]).val)
    (hc : columnIndex.val = ((assignment root::rest)[cursor]).val) :
    ∀ row : Fin dimension, (current.set rowIndex columnIndex).val[row.val]!.val =
      (Assignment.tracePrefixValue assignment (Assignment.augmentTrace assignment (assignment root::rest)) parent (assignment root::rest) (cursor+1) row).val := by
  intro row
  rw [Assignment.tracePrefixValue_succ assignment (Assignment.augmentTrace assignment (assignment root::rest)) parent (assignment root::rest) cursor hi row]
  by_cases he : row = parent (assignment root::rest)[cursor]
  · rw [ite_eq_left he]
    have hRow : row.val = rowIndex.val := (congrArg Fin.val he).trans hr.symm
    have hf : Assignment.augmentTrace assignment (assignment root::rest) row = (assignment root::rest)[cursor] := by
      rw [he]
      exact Assignment.augmentTrace_predecessor assignment parent root rest ht hn _ (List.getElem_mem hi)
    rw [hRow,vec_set_self current rowIndex columnIndex (by rw [hl,hr]; exact (parent (assignment root::rest)[cursor]).isLt),hf]
    exact hc
  · rw [ite_eq_right he]
    have hOther : rowIndex.val ≠ row.val := by
      intro hh
      apply he
      exact Fin.ext (hh.symm.trans hr)
    rw [vec_set_other current rowIndex columnIndex row.val (by rw [hl]; exact row.isLt) hOther]
    exact hValues row

theorem flip_initial_invariant (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (target : Usize)
    (hc : current.val = completed.val) (ht : target.val = (assignment root).val) :
    FlipInvariant dimension assignment parent (assignment root::rest) current target 0#usize false none := by
  refine {
    length := by simpa only [alloc.vec.Vec.length,hc] using input.completed_length
    values := ?_
    cursor_le := by simp only [UScalar.ofNatCore_val_eq]; omega
    column_bound := by rw [ht]; exact (assignment root).isLt
    active_column := ?_
    finished_exact := ?_
    failure_none := rfl
  }
  · intro row
    simpa only [hc,UScalar.ofNatCore_val_eq,Assignment.tracePrefixValue_zero] using input.completed_values row
  · intro _
    refine ⟨by simp only [UScalar.ofNatCore_val_eq,List.length_cons]; omega,?_⟩
    simpa only [UScalar.ofNatCore_val_eq,List.getElem_cons_zero] using ht
  · constructor
    · intro hh
      cases hh
    · intro hh
      simp only [UScalar.ofNatCore_val_eq,List.length_cons] at hh
      omega

end SubtreeProofs.Rust.SparseSearch

end
