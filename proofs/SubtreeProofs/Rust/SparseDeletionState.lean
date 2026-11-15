module

public import SubtreeProofs.Rust.SparseDeletionData
public import SubtreeProofs.Rust.SparseAugmentationEntrypoint
import Mathlib.Tactic

/-!
# Actual compact sparse-deletion numeric state

The original views use an explicit finite dimension so the original and compact
source buffers can be related without equating their dependent vertex types.
Their values are read from the actual input; no optimum or numeric success
certificate is hidden in these representation maps.
-/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

open AssignmentVertexDeletion AssignmentNumericBounds

def originalAllowed {n : Nat} (cost : Slice (alloc.vec.Vec (Option I64))) (row column : Fin n) : Prop :=
  (cost.val[row.val]!).val[column.val]! ≠ none

def originalMatrix {n : Nat} (cost : Slice (alloc.vec.Vec (Option I64))) (row column : Fin n) : ℤ :=
  (((cost.val[row.val]!).val[column.val]!).map IScalar.val).getD 0

def originalPotential {n : Nat} (values : Slice I128) (row : Fin n) : ℤ :=
  values.val[row.val]!.val

/-- Physical projected cells and potentials realize the independently indexed
surviving problem at every actual compact source vertex. -/
theorem projected_views {n : Nat} (removed : Fin (n+1))
    (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128) (vertices : Slice Usize)
    (projectedCost : alloc.vec.Vec (alloc.vec.Vec (Option I64))) (projectedRows projectedColumns : alloc.vec.Vec I128)
    (hVertices : RepresentsVertices removed vertices)
    (hCost : projectedCost.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!)))
    (hRows : projectedRows.val = vertices.val.map (fun vertex => rows.val[vertex.val]!))
    (hColumns : projectedColumns.val = vertices.val.map (fun vertex => columns.val[vertex.val]!))
    (hLength : (alloc.vec.Vec.deref projectedCost).length = n) :
    let equiv : SparseCut.Vertex (alloc.vec.Vec.deref projectedCost) ≃ Fin n := finCongr hLength
    (∀ row column, SparseCut.allowed (alloc.vec.Vec.deref projectedCost) row column ↔
      originalAllowed (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column))) ∧
    (∀ row column, SparseCut.matrix (alloc.vec.Vec.deref projectedCost) row column =
      originalMatrix (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column))) ∧
    (∀ row, SparseCut.potentialAt (alloc.vec.Vec.deref projectedCost) (alloc.vec.Vec.deref projectedRows) row =
      originalPotential (n := n+1) rows (removed.succAbove (equiv row))) ∧
    (∀ column, SparseCut.potentialAt (alloc.vec.Vec.deref projectedCost) (alloc.vec.Vec.deref projectedColumns) column =
      originalPotential (n := n+1) columns (removed.succAbove (equiv column))) := by
  dsimp only
  let equiv : SparseCut.Vertex (alloc.vec.Vec.deref projectedCost) ≃ Fin n := finCongr hLength
  have hDeref : (alloc.vec.Vec.deref projectedCost).val = projectedCost.val := by
    simp only [alloc.vec.Vec.deref,Slice.from_val]
  have hPotential (values : alloc.vec.Vec I128) (vertex : SparseCut.Vertex (alloc.vec.Vec.deref projectedCost)) :
      SparseCut.potentialAt (alloc.vec.Vec.deref projectedCost) (alloc.vec.Vec.deref values) vertex = values.val[vertex.val]!.val := by
    unfold SparseCut.potentialAt
    have hd : (alloc.vec.Vec.deref values).val = values.val := by simp only [alloc.vec.Vec.deref,Slice.from_val]
    rw [hd]
  have hCells : ∀ row column : SparseCut.Vertex (alloc.vec.Vec.deref projectedCost),
      ((alloc.vec.Vec.deref projectedCost).val[row.val]!).val[column.val]! =
        (cost.val[(removed.succAbove (equiv row)).val]!).val[(removed.succAbove (equiv column)).val]! := by
    intro row column
    rw [hDeref]
    simpa only [equiv,finCongr_apply_coe] using
      projected_cell removed cost vertices projectedCost hVertices hCost (equiv row) (equiv column)
  refine ⟨?_,?_,?_,?_⟩
  · intro row column
    unfold SparseCut.allowed originalAllowed
    rw [hCells row column]
  · intro row column
    unfold SparseCut.matrix originalMatrix
    rw [hCells row column]
  · intro row
    have h := projected_potential removed rows vertices projectedRows hVertices hRows (equiv row)
    have hv : (equiv row).val = row.val := finCongr_apply_coe hLength row
    rw [hv] at h
    rw [hPotential]
    unfold originalPotential
    exact h
  · intro column
    have h := projected_potential removed columns vertices projectedColumns hVertices hColumns (equiv column)
    have hv : (equiv column).val = column.val := finCongr_apply_coe hLength column
    rw [hv] at h
    rw [hPotential]
    unfold originalPotential
    exact h

/-- The existing two-sided numeric deletion theorem transfers to the actual
projected source buffers. Its premises concern the old independently feasible
state; the new envelope, accounting and dimension budget are conclusions. -/
theorem projected_numeric_state {n : Nat} (removed : Fin (n+1))
    (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (projectedCost : Slice (alloc.vec.Vec (Option I64))) (projectedRows projectedColumns : alloc.vec.Vec I128)
    (equiv : SparseCut.Vertex projectedCost ≃ Fin n)
    (hEdges : ∀ row column, SparseCut.allowed projectedCost row column ↔
      originalAllowed (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)))
    (hMatrix : ∀ row column, SparseCut.matrix projectedCost row column =
      originalMatrix (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)))
    (hRows : ∀ row, SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedRows) row =
      originalPotential (n := n+1) rows (removed.succAbove (equiv row)))
    (hColumns : ∀ column, SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedColumns) column =
      originalPotential (n := n+1) columns (removed.succAbove (equiv column)))
    (initialRows initialColumns : Fin (n+1) → ℤ) (increment : ℤ)
    (hIdentity : ∀ vertex : Fin (n+1), originalAllowed (n := n+1) cost vertex vertex)
    (hZero : originalMatrix (n := n+1) cost removed removed = 0)
    (hInitialRow : initialRows removed = 0) (hInitialColumn : initialColumns removed = 0)
    (hRowLower : ∀ row, -costMagnitude ≤ initialRows row) (hColumnLower : ∀ column, -costMagnitude ≤ initialColumns column)
    (hUpper : ∀ row column : Fin (n+1), originalAllowed (n := n+1) cost row column → originalMatrix (n := n+1) cost row column ≤ 0)
    (hFeasible : Assignment.FeasibleOn (originalAllowed (n := n+1) cost) (originalMatrix (n := n+1) cost) (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns))
    (hEnvelope : Assignment.BiEnvelope initialRows initialColumns (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) increment)
    (hAccount : Assignment.dualValue (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) = Assignment.dualValue initialRows initialColumns+increment) :
    let next := increment-(originalPotential (n := n+1) rows removed+originalPotential (n := n+1) columns removed)
    let initialRows' := fun row => initialRows (removed.succAbove (equiv row))
    let initialColumns' := fun column => initialColumns (removed.succAbove (equiv column))
    Assignment.FeasibleOn (SparseCut.allowed projectedCost) (SparseCut.matrix projectedCost)
      (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedRows)) (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedColumns)) ∧
    Assignment.BiEnvelope initialRows' initialColumns'
      (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedRows)) (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedColumns)) next ∧
    Assignment.dualValue (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedRows))
      (SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedColumns)) = Assignment.dualValue initialRows' initialColumns'+next ∧
    next ≤ 2*(n : ℤ)*costMagnitude := by
  dsimp only
  obtain ⟨hf,he,ha,hb⟩ := compact_deletion_state (originalAllowed (n := n+1) cost) (originalMatrix (n := n+1) cost)
    initialRows initialColumns (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) increment costMagnitude removed
    hIdentity hZero hInitialRow hInitialColumn hRowLower hColumnLower hUpper hFeasible hEnvelope hAccount
  have hr : SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedRows) =
      fun row => originalPotential (n := n+1) rows (removed.succAbove (equiv row)) := funext hRows
  have hc : SparseCut.potentialAt projectedCost (alloc.vec.Vec.deref projectedColumns) =
      fun column => originalPotential (n := n+1) columns (removed.succAbove (equiv column)) := funext hColumns
  have hm : SparseCut.matrix projectedCost =
      fun row column => originalMatrix (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)) := by
    funext row column
    exact hMatrix row column
  have hd : SparseCut.allowed projectedCost =
      fun row column => originalAllowed (n := n+1) cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)) := by
    funext row column
    exact propext (hEdges row column)
  rw [hr,hc,hm,hd]
  refine ⟨hf.reindex equiv,he.reindex equiv,?_,hb⟩
  rw [Assignment.dualValue_reindex equiv
      (fun row : Fin n => originalPotential rows (removed.succAbove row))
      (fun column : Fin n => originalPotential columns (removed.succAbove column)),
    Assignment.dualValue_reindex equiv
      (fun row : Fin n => initialRows (removed.succAbove row))
      (fun column : Fin n => initialColumns (removed.succAbove column))]
  exact ha

end SubtreeProofs.Rust.SparseDeletion

end
