module

public import SubtreeProofs.Rust.SparseDeletionState
import Mathlib.Tactic

/-! # Actual sparse right-vertex/copy deletion caller -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

open AssignmentVertexDeletion AssignmentNumericBounds

/-- Independently meaningful old feasible/tight state and the paper's numeric
initialization invariant. No source success, repair path or new optimum is a
premise. The identity/zero-baseline hypotheses hold for copied graphs. -/
structure DeletionReady {n : Nat} (cost : Slice (alloc.vec.Vec (Option I64)))
    (rows columns : Slice I128) (completed : Slice Usize) (rawRemoved : Usize)
    (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (initialRows initialColumns : Fin (n+1) → ℤ) (increment : ℤ) : Prop where
  cost_dimension : cost.length = n+1
  rows_length : rows.length = n+1
  columns_length : columns.length = n+1
  completed_length : completed.length = n+1
  square : SparseCut.Square cost
  size_bound : cost.length ≤ U32.max
  removed_index : rawRemoved.val = removed.val
  completed_values : ∀ row : Fin (n+1), completed.val[row.val]!.val = (assignment row).val
  identity_allowed : ∀ vertex : Fin (n+1), originalAllowed cost vertex vertex
  deleted_zero : originalMatrix cost removed removed = 0
  initial_row_zero : initialRows removed = 0
  initial_column_zero : initialColumns removed = 0
  initial_rows : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0
  initial_columns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0
  nonpositive_cost : ∀ row column : Fin (n+1), originalAllowed cost row column → originalMatrix cost row column ≤ 0
  feasible : Assignment.FeasibleOn (originalAllowed (n := n+1) cost) (originalMatrix (n := n+1) cost)
    (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns)
  allowed : Assignment.Compatible (originalAllowed (n := n+1) cost) assignment
  tight : Assignment.Tight (originalMatrix (n := n+1) cost)
    (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) assignment
  envelope : Assignment.BiEnvelope initialRows initialColumns
    (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) increment
  account : Assignment.dualValue (originalPotential (n := n+1) rows) (originalPotential (n := n+1) columns) =
    Assignment.dualValue initialRows initialColumns+increment

/-- Source output retains original labels and a feasible tight independently
minimum assignment of the surviving graph. The repaired flag records exactly
whether the deleted old vertex was nonfixed. -/
structure CorrectDeletion {n : Nat} (cost : Slice (alloc.vec.Vec (Option I64)))
    (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (output : sparse_deletion.SparseDeletedAssignment) : Prop where
  vertices_model : RepresentsVertices removed (alloc.vec.Vec.deref output.vertices)
  vertices_length : output.vertices.length = n
  assignment_length : output.column_for_row.length = n
  rows_length : output.rows.length = n
  columns_length : output.columns.length = n
  repaired_eq : output.repaired = decide (assignment removed ≠ removed)
  optimum : ∃ chosen : Equiv.Perm (Fin n),
    Assignment.IsMinimumOn (fun row column => originalAllowed cost (removed.succAbove row) (removed.succAbove column))
      (fun row column => originalMatrix cost (removed.succAbove row) (removed.succAbove column)) chosen ∧
    (∀ row : Fin n, output.column_for_row.val[row.val]!.val = (removed.succAbove (chosen row)).val) ∧
    Assignment.FeasibleOn (fun row column => originalAllowed cost (removed.succAbove row) (removed.succAbove column))
      (fun row column => originalMatrix cost (removed.succAbove row) (removed.succAbove column))
      (originalPotential (n := n) (alloc.vec.Vec.deref output.rows))
      (originalPotential (n := n) (alloc.vec.Vec.deref output.columns)) ∧
    Assignment.Tight (fun row column => originalMatrix cost (removed.succAbove row) (removed.succAbove column))
      (originalPotential (n := n) (alloc.vec.Vec.deref output.rows))
      (originalPotential (n := n) (alloc.vec.Vec.deref output.columns)) chosen

/-- The actual public caller projects, reuses or repairs once, and exports an
independently minimum surviving assignment in original input coordinates.
Machine arithmetic/indices/termination follow from the old numeric state.
This is the exact reference caller, without a priority-queue runtime claim. -/
theorem repair_deleted_sparse_vertex_spec {n : Nat}
    (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (completed : Slice Usize) (rawRemoved : Usize)
    (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (initialRows initialColumns : Fin (n+1) → ℤ) (increment : ℤ)
    (input : DeletionReady cost rows columns completed rawRemoved assignment removed initialRows initialColumns increment) :
    sparse_deletion.repair_deleted_sparse_vertex cost rows columns completed rawRemoved ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ CorrectDeletion cost assignment removed output ⦄ := by
  have hrLen : Slice.len rows = Slice.len cost := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,Slice.len_val,input.rows_length,input.cost_dimension])
  have hcLen : Slice.len columns = Slice.len cost := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,Slice.len_val,input.columns_length,input.cost_dimension])
  have hpLen : Slice.len completed = Slice.len cost := UScalar.eq_of_val_eq (by
    rw [Slice.len_val,Slice.len_val,input.completed_length,input.cost_dimension])
  have hRemoved : rawRemoved.val < cost.length := by
    rw [input.removed_index,input.cost_dimension]
    exact removed.isLt
  unfold sparse_deletion.repair_deleted_sparse_vertex
  simp only [hrLen,hcLen,hpLen,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (SparseCut.square_shape_spec cost)
  intro shape hShape
  simp only [hShape.mpr input.square,↓reduceIte]
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
  intro limit hLimit
  have hLimitVal : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
  have hSize : ¬ Slice.len cost > limit := by have hl := Slice.len_val cost; have hb := input.size_bound; scalar_tac
  have hRemovedBound : ¬ rawRemoved ≥ Slice.len cost := by have hl := Slice.len_val cost; scalar_tac
  simp only [hSize,hRemovedBound,↓reduceIte]
  apply WP.spec_bind (SparseSearch.inverse_completed_dimension_spec completed (n+1) input.completed_length assignment input.completed_values)
  rintro result ⟨inverse,rfl,hInverseLength,hInverseValues⟩
  simp only [alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec inverse rawRemoved (by rw [hInverseLength,input.removed_index]; exact removed.isLt))
  intro freeRow hFreeRow
  have hFreeRowVal : freeRow.val = (assignment.symm removed).val := by
    have hh : freeRow = inverse.val[rawRemoved.val]! := by
      simpa only [getElem!_pos inverse.val rawRemoved.val (by rw [← alloc.vec.Vec.length,hInverseLength,input.removed_index]; exact removed.isLt)] using hFreeRow
    rw [hh,input.removed_index,hInverseValues removed]
  apply WP.spec_bind (Slice.index_usize_spec completed rawRemoved (by rw [input.completed_length,input.removed_index]; exact removed.isLt))
  intro freeColumn hFreeColumn
  have hFreeColumnVal : freeColumn.val = (assignment removed).val := by
    have hh : freeColumn = completed.val[rawRemoved.val]! := by
      simpa only [getElem!_pos completed.val rawRemoved.val (by rw [← Slice.length,input.completed_length,input.removed_index]; exact removed.isLt)] using hFreeColumn
    rw [hh,input.removed_index,input.completed_values removed]
  apply WP.spec_bind (surviving_vertices_canonical_spec removed (Slice.len cost) rawRemoved
    ((Slice.len_val cost).trans input.cost_dimension) input.removed_index)
  intro vertices hVertices
  let selected := alloc.vec.Vec.deref vertices
  have hVertices' : RepresentsVertices removed selected := hVertices
  have hVertexLength : vertices.length = n := by
    simpa only [selected,alloc.vec.Vec.deref,Slice.length,Slice.from_val] using vertices_length removed selected hVertices'
  have hVertexBounds : ∀ vertex ∈ selected.val, vertex.val < n+1 := fun vertex hv => (vertices_bounds removed selected hVertices' vertex hv).1
  apply WP.spec_bind (project_cost_spec cost selected input.square (by intro vertex hv; rw [input.cost_dimension]; exact hVertexBounds vertex hv))
  intro projectedCost hCost
  apply WP.spec_bind (project_potentials_spec rows selected (by intro vertex hv; rw [input.rows_length]; exact hVertexBounds vertex hv))
  intro projectedRows hRows
  apply WP.spec_bind (project_potentials_spec columns selected (by intro vertex hv; rw [input.columns_length]; exact hVertexBounds vertex hv))
  intro projectedColumns hColumns
  apply WP.spec_bind (complete_surviving_permutation_spec assignment removed completed selected rawRemoved freeRow freeColumn
    input.completed_length input.completed_values hVertices' input.removed_index hFreeRowVal hFreeColumnVal)
  rintro result ⟨seed,rfl,hSeedLength,hSeed⟩
  have hProjectedRowsLength := projected_potential_length removed rows selected projectedRows hVertices' hRows
  have hProjectedColumnsLength := projected_potential_length removed columns selected projectedColumns hVertices' hColumns
  have hProjectedLength : (alloc.vec.Vec.deref projectedCost).length = n := by
    simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using
      (projected_length cost selected projectedCost hCost).trans (vertices_length removed selected hVertices')
  have hRowModel : originalPotential (n := n) (alloc.vec.Vec.deref projectedRows) =
      fun row => originalPotential rows (removed.succAbove row) := by
    funext row
    simpa only [originalPotential,alloc.vec.Vec.deref,Slice.from_val] using
      projected_potential removed rows selected projectedRows hVertices' hRows row
  have hColumnModel : originalPotential (n := n) (alloc.vec.Vec.deref projectedColumns) =
      fun column => originalPotential columns (removed.succAbove column) := by
    funext column
    simpa only [originalPotential,alloc.vec.Vec.deref,Slice.from_val] using
      projected_potential removed columns selected projectedColumns hVertices' hColumns column
  by_cases hPaired : assignment removed = removed
  · have hFreeEq : freeColumn = rawRemoved := UScalar.eq_of_val_eq (by rw [hFreeColumnVal,hPaired,input.removed_index])
    simp only [hFreeEq,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
    apply WP.spec_bind (original_columns_permutation_spec removed (compactAssignment assignment removed)
      (alloc.vec.Vec.deref seed) selected (by simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using hSeedLength)
      (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hSeed) hVertices')
    rintro result ⟨exported,rfl,hExportedLength,hExported⟩
    obtain ⟨hMinimum,hTight⟩ := compact_paired_optimum (originalAllowed cost) (originalMatrix cost)
      (originalPotential rows) (originalPotential columns) assignment removed hPaired input.feasible input.allowed input.tight
    apply (WP.spec_ok _).mpr
    refine ⟨⟨vertices,exported,projectedRows,projectedColumns,false⟩,rfl,{
      vertices_model := hVertices
      vertices_length := hVertexLength
      assignment_length := hExportedLength
      rows_length := hProjectedRowsLength
      columns_length := hProjectedColumnsLength
      repaired_eq := by simp [hPaired]
      optimum := ?_ }⟩
    refine ⟨compactAssignment assignment removed,hMinimum,hExported,?_,?_⟩
    · rw [hRowModel,hColumnModel]
      exact fun row column he => input.feasible (removed.succAbove row) (removed.succAbove column) he
    · rw [hRowModel,hColumnModel]
      exact hTight
  · have hFreeNe : freeColumn ≠ rawRemoved := by
      intro he
      apply hPaired
      exact Fin.ext (by rw [← hFreeColumnVal,he,input.removed_index])
    simp only [bne_iff_ne.mpr hFreeNe,↓reduceIte]
    apply WP.spec_bind (compact_index_remaining_spec removed (AssignmentVertexDeletion.freeRow assignment removed hPaired) freeRow rawRemoved hFreeRowVal input.removed_index)
    rintro result ⟨rootIndex,rfl,hRoot⟩
    let projected := alloc.vec.Vec.deref projectedCost
    let equiv : SparseCut.Vertex projected ≃ Fin n := finCongr hProjectedLength
    let initialRows' := fun row => initialRows (removed.succAbove (equiv row))
    let initialColumns' := fun column => initialColumns (removed.succAbove (equiv column))
    let next := increment-(originalPotential rows removed+originalPotential columns removed)
    let compact := compactAssignment assignment removed
    let rawAssignment : Equiv.Perm (SparseCut.Vertex projected) := equiv.trans (compact.trans equiv.symm)
    let root := equiv.symm (compactFree assignment removed hPaired)
    have hEquiv : ∀ row, (equiv row).val = row.val := fun row => finCongr_apply_coe hProjectedLength row
    have hInverseEquiv : ∀ row, (equiv.symm row).val = row.val := by
      intro row
      simpa only [equiv,finCongr_symm] using finCongr_apply_coe hProjectedLength.symm row
    obtain ⟨hEdges,hMatrix,hActualRows,hActualColumns⟩ := projected_views removed cost rows columns selected
      projectedCost projectedRows projectedColumns hVertices' hCost hRows hColumns hProjectedLength
    have hNumeric := projected_numeric_state removed cost rows columns projected projectedRows projectedColumns equiv
      hEdges hMatrix hActualRows hActualColumns initialRows initialColumns increment input.identity_allowed input.deleted_zero
      input.initial_row_zero input.initial_column_zero (fun row => (input.initial_rows row).1)
      (fun column => (input.initial_columns column).1) input.nonpositive_cost input.feasible input.envelope input.account
    obtain ⟨hFeasible,hEnvelope,hAccount,_⟩ := hNumeric
    have hSeedRaw : ∀ row : SparseCut.Vertex projected,
        seed.val[row.val]!.val = (rawAssignment row).val := by
      intro row
      change seed.val[row.val]!.val = (equiv.symm (compact (equiv row))).val
      rw [hInverseEquiv]
      have h := hSeed (equiv row)
      rw [hEquiv row] at h
      exact h
    have hSeedFacts := compact_seed (originalAllowed cost) (originalMatrix cost)
      (originalPotential rows) (originalPotential columns) assignment removed hPaired input.allowed input.tight
    have hAway : ∀ row : SparseCut.Vertex projected, row ≠ root → equiv row ≠ compactFree assignment removed hPaired := by
      intro row hr he
      exact hr (equiv.injective (by simpa only [root,Equiv.apply_symm_apply] using he))
    have hAllowed : ∀ row : SparseCut.Vertex projected, row ≠ root → SparseCut.allowed projected row (rawAssignment row) := by
      intro row hr
      apply (hEdges row (rawAssignment row)).mpr
      simpa only [rawAssignment,equiv,Equiv.trans_apply,Equiv.symm_apply_apply,Equiv.apply_symm_apply,compact] using (hSeedFacts (equiv row) (hAway row hr)).1
    have hTight : ∀ row : SparseCut.Vertex projected, row ≠ root →
        SparseCut.potentialAt projected (alloc.vec.Vec.deref projectedRows) row+
          SparseCut.potentialAt projected (alloc.vec.Vec.deref projectedColumns) (rawAssignment row) = SparseCut.matrix projected row (rawAssignment row) := by
      intro row hr
      rw [hActualRows row,hActualColumns (rawAssignment row),hMatrix row (rawAssignment row)]
      simpa only [rawAssignment,equiv,Equiv.trans_apply,Equiv.apply_symm_apply,compact] using (hSeedFacts (equiv row) (hAway row hr)).2
    have hUpper : ∀ row column : SparseCut.Vertex projected, SparseCut.allowed projected row column → SparseCut.matrix projected row column ≤ 0 := by
      intro row column he
      rw [hMatrix row column]
      exact input.nonpositive_cost _ _ ((hEdges row column).mp he)
    have hCompatible : ∃ chosen : Equiv.Perm (SparseCut.Vertex projected), Assignment.Compatible (SparseCut.allowed projected) chosen := by
      refine ⟨1,?_⟩
      intro row
      exact (hEdges row row).mpr (input.identity_allowed _)
    apply WP.spec_bind (SparseSearch.augment_sparse_permutation_spec projected projectedRows projectedColumns
      (alloc.vec.Vec.deref seed) rootIndex rawAssignment root
      (by simpa only [root,hInverseEquiv,compactFree] using hRoot)
      (hProjectedRowsLength.trans hProjectedLength.symm) (hProjectedColumnsLength.trans hProjectedLength.symm)
      (by
        have hl : (alloc.vec.Vec.deref seed).length = seed.length := by simp only [alloc.vec.Vec.deref,Slice.length,Slice.from_val]
        exact hl.trans (hSeedLength.trans hProjectedLength.symm))
      (by
        intro row
        have hv : (alloc.vec.Vec.deref seed).val = seed.val := by simp only [alloc.vec.Vec.deref,Slice.from_val]
        rw [hv]
        exact hSeedRaw row) (projected_square cost selected projectedCost hCost)
      (by rw [hProjectedLength]; have hb := input.size_bound; rw [input.cost_dimension] at hb; omega)
      initialRows' initialColumns' next (fun row => input.initial_rows _) (fun column => input.initial_columns _)
      hEnvelope hAccount hFeasible hAllowed hTight hUpper hCompatible)
    rintro result ⟨augmented,rfl,hAugmented⟩
    obtain ⟨hSearch,rest,_,_,hAssignmentLength,hAssignment,hMinimum,hFinalTight,_⟩ := hAugmented
    let chosen := Assignment.augmentTrace rawAssignment (rawAssignment root::rest)
    let finiteChosen : Equiv.Perm (Fin n) := equiv.symm.trans (chosen.trans equiv)
    have hFinalValues : ∀ row : Fin n, augmented.column_for_row.val[row.val]!.val = (finiteChosen row).val := by
      intro row
      have h := hAssignment (equiv.symm row)
      rw [hInverseEquiv row] at h
      simpa only [finiteChosen,Equiv.trans_apply,hEquiv,chosen] using h
    apply WP.spec_bind (original_columns_permutation_spec removed finiteChosen
      (alloc.vec.Vec.deref augmented.column_for_row) selected
      (by simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val] using hAssignmentLength.trans hProjectedLength)
      (by simpa only [alloc.vec.Vec.deref,Slice.from_val] using hFinalValues) hVertices')
    rintro result ⟨exported,rfl,hExportedLength,hExported⟩
    have hEdgesEq : SparseCut.allowed projected = fun row column => originalAllowed cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)) := by
      funext row column
      exact propext (hEdges row column)
    have hMatrixEq : SparseCut.matrix projected = fun row column => originalMatrix cost (removed.succAbove (equiv row)) (removed.succAbove (equiv column)) := by
      funext row column
      exact hMatrix row column
    have hNewRows : (fun row : Fin n => SparseCut.potentialAt projected (alloc.vec.Vec.deref augmented.search.rows) (equiv.symm row)) =
        originalPotential (n := n) (alloc.vec.Vec.deref augmented.search.rows) := by
      funext row
      unfold SparseCut.potentialAt originalPotential
      rw [hInverseEquiv row]
    have hNewColumns : (fun column : Fin n => SparseCut.potentialAt projected (alloc.vec.Vec.deref augmented.search.columns) (equiv.symm column)) =
        originalPotential (n := n) (alloc.vec.Vec.deref augmented.search.columns) := by
      funext column
      unfold SparseCut.potentialAt originalPotential
      rw [hInverseEquiv column]
    have hMinimum' := hMinimum.reindex equiv.symm
    have hFeasible' := hSearch.feasible.reindex equiv.symm
    have hTight' := hFinalTight.reindex equiv.symm
    simp only [hEdgesEq,hMatrixEq,Equiv.apply_symm_apply,hNewRows,hNewColumns] at hMinimum' hFeasible' hTight'
    apply (WP.spec_ok _).mpr
    refine ⟨⟨vertices,exported,augmented.search.rows,augmented.search.columns,true⟩,rfl,{
      vertices_model := hVertices
      vertices_length := hVertexLength
      assignment_length := hExportedLength
      rows_length := hSearch.rows_length.trans hProjectedLength
      columns_length := hSearch.columns_length.trans hProjectedLength
      repaired_eq := by simp [hPaired]
      optimum := ⟨finiteChosen,hMinimum',hExported,hFeasible',hTight'⟩ }⟩

end SubtreeProofs.Rust.SparseDeletion

end
