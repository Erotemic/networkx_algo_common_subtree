module

public import SubtreeProofs.Rust.SparseDeletionWarmStart
public import SubtreeProofs.Rust.SparseCutAdjustment
import Mathlib.Tactic

/-! # Actual projected cells and potentials retain original finite coordinates -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

open AssignmentVertexDeletion

/-- Both source projection axes expand to the original `succAbove` vertices. -/
theorem projected_cell {n : Nat} (removed : Fin (n+1))
    (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (output : alloc.vec.Vec (alloc.vec.Vec (Option I64)))
    (hVertices : RepresentsVertices removed vertices)
    (hOutput : output.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!)))
    (row column : Fin n) :
    (output.val[row.val]!).val[column.val]! =
      (cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]! := by
  have hr : row.val < vertices.length := by rw [vertices_length removed vertices hVertices]; exact row.isLt
  have hc : column.val < vertices.length := by rw [vertices_length removed vertices hVertices]; exact column.isLt
  rw [projected_row cost vertices output hOutput row.val hr,
    mapped_get _ vertices.val column.val hc,vertex_at removed vertices hVertices row,
    vertex_at removed vertices hVertices column]

/-- Projecting an actual potential vector preserves its signed value under
exactly the same original-coordinate expansion as the cost matrix. -/
theorem projected_potential {n : Nat} (removed : Fin (n+1))
    (values : Slice I128) (vertices : Slice Usize) (output : alloc.vec.Vec I128)
    (hVertices : RepresentsVertices removed vertices)
    (hOutput : output.val = vertices.val.map (fun vertex => values.val[vertex.val]!))
    (row : Fin n) :
    output.val[row.val]!.val = values.val[(removed.succAbove row).val]!.val := by
  have hi : row.val < vertices.length := by rw [vertices_length removed vertices hVertices]; exact row.isLt
  rw [hOutput,mapped_get _ vertices.val row.val hi,vertex_at removed vertices hVertices row]

theorem projected_potential_length {n : Nat} (removed : Fin (n+1))
    (values : Slice I128) (vertices : Slice Usize) (output : alloc.vec.Vec I128)
    (hVertices : RepresentsVertices removed vertices)
    (hOutput : output.val = vertices.val.map (fun vertex => values.val[vertex.val]!)) :
    output.length = n := by
  have h := congrArg List.length hOutput
  simpa only [List.length_map,vertices_length removed vertices hVertices] using h

/-- An independently minimum projected source assignment remains minimum in
the original surviving finite coordinates. This transports the optimization
objective, not merely the returned scalar index list. -/
theorem projected_minimum {n : Nat} (removed : Fin (n+1))
    (cost : Slice (alloc.vec.Vec (Option I64))) (vertices : Slice Usize)
    (output : alloc.vec.Vec (alloc.vec.Vec (Option I64)))
    (hVertices : RepresentsVertices removed vertices)
    (hOutput : output.val.map alloc.vec.Vec.val = vertices.val.map (fun row =>
      vertices.val.map (fun column => (cost.val[row.val]!).val[column.val]!)))
    (assignment : Equiv.Perm (SparseCut.Vertex (alloc.vec.Vec.deref output)))
    (hMinimum : Assignment.IsMinimumOn (SparseCut.allowed (alloc.vec.Vec.deref output))
      (SparseCut.matrix (alloc.vec.Vec.deref output)) assignment) :
    let hLength : (alloc.vec.Vec.deref output).length = n := by
      simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using
        (projected_length cost vertices output hOutput).trans (vertices_length removed vertices hVertices)
    let equiv : Fin n ≃ SparseCut.Vertex (alloc.vec.Vec.deref output) := finCongr hLength.symm
    Assignment.IsMinimumOn
      (fun row column : Fin n => (cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]! ≠ none)
      (fun row column : Fin n => (((cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]!).map IScalar.val).getD 0)
      (equiv.trans (assignment.trans equiv.symm)) := by
  dsimp only
  let hLength : (alloc.vec.Vec.deref output).length = n := by
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using
      (projected_length cost vertices output hOutput).trans (vertices_length removed vertices hVertices)
  let equiv : Fin n ≃ SparseCut.Vertex (alloc.vec.Vec.deref output) := finCongr hLength.symm
  have hDeref : (alloc.vec.Vec.deref output).val = output.val := by
    simp only [alloc.vec.Vec.deref,Slice.from_val]
  have hCells : ∀ row column : Fin n,
      ((alloc.vec.Vec.deref output).val[(equiv row).val]!).val[(equiv column).val]! =
        (cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]! := by
    intro row column
    rw [hDeref]
    simpa only [equiv,finCongr_apply_coe] using projected_cell removed cost vertices output hVertices hOutput row column
  have hEdges : (fun row column : Fin n => SparseCut.allowed (alloc.vec.Vec.deref output) (equiv row) (equiv column)) =
      (fun row column : Fin n => (cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]! ≠ none) := by
    funext row column
    unfold SparseCut.allowed
    rw [hCells row column]
  have hMatrix : (fun row column : Fin n => SparseCut.matrix (alloc.vec.Vec.deref output) (equiv row) (equiv column)) =
      (fun row column : Fin n => (((cost.val[(removed.succAbove row).val]!).val[(removed.succAbove column).val]!).map IScalar.val).getD 0) := by
    funext row column
    unfold SparseCut.matrix
    rw [hCells row column]
  have h := hMinimum.reindex equiv
  rw [hEdges,hMatrix] at h
  exact h

end SubtreeProofs.Rust.SparseDeletion

end
