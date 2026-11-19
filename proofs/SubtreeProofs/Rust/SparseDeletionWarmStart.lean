module

public import SubtreeProofs.Rust.SparseDeletionSeed
public import SubtreeProofs.Rust.SparseDeletionReadback
public import SubtreeProofs.Shared.AssignmentCompactDeletionState
import Mathlib.Tactic

/-!
# Actual sparse-deletion warm starts represent the independent permutation

The source's bypass/free-endpoint choices and compression are related to the
canonical surviving finite vertices. The no-deleted-column precondition of the
source loop follows from permutation injectivity; it is not a supplied success
certificate or a supplied optimum.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

open AssignmentVertexDeletion

/-- The actual increasing survivor vector is represented by Mathlib's
canonical `succAbove` enumeration. -/
def RepresentsVertices {n : Nat} (removed : Fin (n+1)) (vertices : Slice Usize) : Prop :=
  vertices.val.map UScalar.val = (List.finRange n).map (fun i => (removed.succAbove i).val)

theorem vertices_length {n : Nat} (removed : Fin (n+1)) (vertices : Slice Usize)
    (h : RepresentsVertices removed vertices) : vertices.length = n := by
  have hh := congrArg List.length h
  simpa only [List.length_map,List.length_finRange] using hh

theorem vertices_bounds {n : Nat} (removed : Fin (n+1)) (vertices : Slice Usize)
    (h : RepresentsVertices removed vertices) (vertex : Usize) (hv : vertex ∈ vertices.val) :
    vertex.val < n+1 ∧ vertex.val ≠ removed.val := by
  have hm : vertex.val ∈ vertices.val.map UScalar.val := List.mem_map.mpr ⟨vertex,hv,rfl⟩
  rw [h] at hm
  obtain ⟨i,_,hi⟩ := List.mem_map.mp hm
  refine ⟨by rw [← hi]; exact (removed.succAbove i).isLt,?_⟩
  intro he
  exact Fin.succAbove_ne removed i (Fin.ext (hi.trans he))


theorem vertex_at {n : Nat} (removed : Fin (n+1)) (vertices : Slice Usize)
    (h : RepresentsVertices removed vertices) (index : Fin n) :
    vertices.val[index.val]!.val = (removed.succAbove index).val := by
  have hl := vertices_length removed vertices h
  have hi : index.val < vertices.val.length := by change index.val < vertices.length; omega
  have hh := congrArg (fun values : List Nat => values[index.val]!) h
  rw [mapped_get UScalar.val vertices.val index.val hi] at hh
  simpa only [getElem!_pos ((List.finRange n).map (fun i => (removed.succAbove i).val)) index.val
    (by simp only [List.length_map,List.length_finRange]; exact index.isLt),List.getElem_map,List.getElem_finRange,Fin.cast_mk] using hh

/-- The source's enumeration theorem closes the canonical representation
premise used by the projection and warm-start contracts. -/
theorem surviving_vertices_canonical_spec {n : Nat} (removed : Fin (n+1))
    (rawSize rawRemoved : Usize) (hSize : rawSize.val = n+1) (hRemoved : rawRemoved.val = removed.val) :
    sparse_deletion.surviving_vertices rawSize rawRemoved ⦃ result =>
      RepresentsVertices removed (alloc.vec.Vec.deref result) ⦄ := by
  apply WP.spec_mono (surviving_vertices_spec rawSize rawRemoved)
  intro result hResult
  simp only [RepresentsVertices,alloc.vec.Vec.deref,Slice.from_val]
  rw [hResult,hSize,hRemoved]
  exact survivingIndices_canonical removed

/-- Source endpoint selection agrees with bypassing the deleted vertex in
its old permutation cycle, at every actual surviving original row. -/
theorem selectedColumn_bypass {n : Nat} (assignment : Equiv.Perm (Fin (n+1)))
    (removed row : Fin (n+1)) (hSurvivor : row ≠ removed)
    (completed : Slice Usize) (rawRow freeRow freeColumn : Usize)
    (hCompleted : ∀ vertex : Fin (n+1), completed.val[vertex.val]!.val = (assignment vertex).val)
    (hRow : rawRow.val = row.val) (hFreeRow : freeRow.val = (assignment.symm removed).val)
    (hFreeColumn : freeColumn.val = (assignment removed).val) :
    (selectedColumn completed freeRow freeColumn rawRow).val = (bypass assignment removed row).val := by
  by_cases he : rawRow = freeRow
  · have hf : row = assignment.symm removed := Fin.ext (by rw [← hRow,he,hFreeRow])
    simp only [selectedColumn,he,↓reduceIte,hFreeColumn,hf,bypass_free]
  · have hf : row ≠ assignment.symm removed := by
      intro hf
      exact he (UScalar.eq_of_val_eq (by rw [hRow,hf,hFreeRow]))
    simp only [selectedColumn,he,↓reduceIte,hRow,hCompleted,bypass_away assignment removed row hSurvivor hf]

/-- The independent compact permutation's scalar index is exactly the source
skip-index formula applied to the original bypass column. -/
theorem compactAssignment_index {n : Nat} (assignment : Equiv.Perm (Fin (n+1)))
    (removed : Fin (n+1)) (row : Fin n) :
    (compactAssignment assignment removed row).val =
      if (bypass assignment removed (removed.succAbove row)).val < removed.val then
        (bypass assignment removed (removed.succAbove row)).val
      else (bypass assignment removed (removed.succAbove row)).val-1 := by
  have h := remainingEquiv_symm_val removed (remainingEquiv removed (compactAssignment assignment removed row))
  simpa only [Equiv.symm_apply_apply,compactAssignment_value] using h

/-- Actual source bypass completion succeeds and returns the independent
surviving permutation, rather than assuming the loop's survival premise. -/
theorem complete_surviving_permutation_spec {n : Nat} (assignment : Equiv.Perm (Fin (n+1)))
    (removed : Fin (n+1)) (completed vertices : Slice Usize) (rawRemoved freeRow freeColumn : Usize)
    (hLength : completed.length = n+1)
    (hCompleted : ∀ row : Fin (n+1), completed.val[row.val]!.val = (assignment row).val)
    (hVertices : RepresentsVertices removed vertices) (hRemoved : rawRemoved.val = removed.val)
    (hFreeRow : freeRow.val = (assignment.symm removed).val) (hFreeColumn : freeColumn.val = (assignment removed).val) :
    sparse_deletion.complete_surviving completed vertices rawRemoved freeRow freeColumn ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ output.length = n ∧
      ∀ row : Fin n, output.val[row.val]!.val = (compactAssignment assignment removed row).val ⦄ := by
  have hRows : ∀ rawRow ∈ vertices.val, rawRow.val < completed.length := by
    intro rawRow hr
    rw [hLength]
    exact (vertices_bounds removed vertices hVertices rawRow hr).1
  have hSurvives : ∀ rawRow ∈ vertices.val, selectedColumn completed freeRow freeColumn rawRow ≠ rawRemoved := by
    intro rawRow hr he
    have hb := vertices_bounds removed vertices hVertices rawRow hr
    let row : Fin (n+1) := ⟨rawRow.val,hb.1⟩
    have hn : row ≠ removed := fun hh => hb.2 (congrArg Fin.val hh)
    have hm := selectedColumn_bypass assignment removed row hn completed rawRow freeRow freeColumn
      hCompleted rfl hFreeRow hFreeColumn
    have hf : bypass assignment removed row = removed := Fin.ext (by rw [← hm,he,hRemoved])
    exact ((bypass_nonremoved assignment removed row).mpr hn) hf
  apply WP.spec_mono (complete_surviving_spec completed vertices rawRemoved freeRow freeColumn hRows hSurvives)
  rintro result ⟨output,rfl,hOutput⟩
  have hl : output.length = n := by
    have hh := congrArg List.length hOutput
    have hv := vertices_length removed vertices hVertices
    simpa only [List.length_map,← hv] using hh
  refine ⟨output,rfl,hl,?_⟩
  intro row
  have hi : row.val < output.val.length := by change row.val < output.length; omega
  have hj : row.val < vertices.val.length := by
    change row.val < vertices.length
    rw [vertices_length removed vertices hVertices]
    exact row.isLt
  have hh := congrArg (fun values : List Nat => values[row.val]!) hOutput
  rw [mapped_get UScalar.val output.val row.val hi,mapped_get _ vertices.val row.val hj] at hh
  rw [hh,compressedValue,hRemoved,
    selectedColumn_bypass assignment removed (removed.succAbove row) (Fin.succAbove_ne removed row)
      completed vertices.val[row.val]! freeRow freeColumn hCompleted (vertex_at removed vertices hVertices row) hFreeRow hFreeColumn]
  exact (compactAssignment_index assignment removed row).symm

/-- A compact permutation exported by the actual checked source loop retains
its original surviving vertex labels. Every read bound follows from the
represented permutation and canonical survivor vector. -/
theorem original_columns_permutation_spec {n : Nat} (removed : Fin (n+1))
    (assignment : Equiv.Perm (Fin n)) (columns vertices : Slice Usize)
    (hLength : columns.length = n)
    (hColumns : ∀ row : Fin n, columns.val[row.val]!.val = (assignment row).val)
    (hVertices : RepresentsVertices removed vertices) :
    sparse_deletion.original_columns columns vertices ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ output.length = n ∧
      ∀ row : Fin n, output.val[row.val]!.val = (removed.succAbove (assignment row)).val ⦄ := by
  have hBounds : ∀ column ∈ columns.val, column.val < vertices.length := by
    intro column hc
    obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hc
    let row : Fin n := ⟨i,by simpa only [hLength] using hi⟩
    have hm := hColumns row
    change columns.val[i]!.val = (assignment row).val at hm
    rw [getElem!_pos columns.val i hi,he] at hm
    rw [hm,vertices_length removed vertices hVertices]
    exact (assignment row).isLt
  apply WP.spec_mono (original_columns_spec columns vertices hBounds)
  rintro result ⟨output,rfl,hOutput⟩
  have hl : output.length = n := by
    have hh := congrArg List.length hOutput
    simpa only [List.length_map,hLength] using hh
  refine ⟨output,rfl,hl,?_⟩
  intro row
  have hi : row.val < columns.val.length := by change row.val < columns.length; rw [hLength]; exact row.isLt
  have hh := congrArg (fun values : List Usize => values[row.val]!) hOutput
  rw [mapped_get (fun column => vertices.val[column.val]!) columns.val row.val hi] at hh
  rw [hh,hColumns row]
  exact vertex_at removed vertices hVertices (assignment row)

end SubtreeProofs.Rust.SparseDeletion

end
