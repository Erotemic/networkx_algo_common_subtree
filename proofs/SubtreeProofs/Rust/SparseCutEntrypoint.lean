module

public import SubtreeProofs.Rust.SparseCutRow
public import SubtreeProofs.Rust.AssignmentEntrypoint
import Mathlib.Tactic

/-! # Actual whole sparse cut scan with original-coordinate minimum witnesses -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

/-- Representation and numeric frame expected from the sparse APM state. The
bounded potentials are the uniform dimension/cost envelope, not a supplied
minimum, path or optimum certificate. -/
structure Input (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) : Prop where
  rows_len : rows.length = cost.length
  columns_len : columns.length = cost.length
  selected_rows_len : selectedRows.length = cost.length
  selected_columns_len : selectedColumns.length = cost.length
  square : Square cost
  size : cost.length ≤ U32.max
  rows_bound : ∀ index, index < cost.length → -potentialBound ≤ rows.val[index]!.val ∧ rows.val[index]!.val ≤ potentialBound
  columns_bound : ∀ index, index < cost.length → -potentialBound ≤ columns.val[index]!.val ∧ columns.val[index]!.val ≤ potentialBound

def matrixRow (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (row : Nat) : List Entry :=
  if selectedRows.val[row]! then
    rowCandidates (alloc.vec.Vec.deref cost.val[row]!) rows.val[row]! columns selectedColumns row (cost.val[row]!).length
  else []

/-- All independently enumerated allowed cut candidates in the original
matrix prefix; their coordinates and reduced costs come from original inputs. -/
def cutCandidates (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (upto : Nat) : List Entry :=
  (List.range upto).flatMap (matrixRow cost rows columns selectedRows selectedColumns)

@[simp] theorem cutCandidates_zero (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) : cutCandidates cost rows columns selectedRows selectedColumns 0 = [] := rfl

theorem cutCandidates_succ (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (row : Nat) :
    cutCandidates cost rows columns selectedRows selectedColumns (row+1) =
      cutCandidates cost rows columns selectedRows selectedColumns row ++ matrixRow cost rows columns selectedRows selectedColumns row := by
  simp only [cutCandidates,List.range_succ,List.flatMap_append,List.flatMap_cons,List.flatMap_nil,List.append_nil]

/-- Every actual outer loop iteration composes its row minimum with the whole
prior candidate family, preserving exact original-coordinate attainment. -/
theorem minimum_sparse_cut_loop_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (n : Usize) (hn : n.val = cost.length)
    (h : Input cost rows columns selectedRows selectedColumns) :
    sparse.minimum_sparse_cut_loop cost rows columns selectedRows selectedColumns n none 0#usize ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ BestAmong output (cutCandidates cost rows columns selectedRows selectedColumns cost.length) ⦄ := by
  unfold sparse.minimum_sparse_cut_loop
  apply loop.spec_decr_nat (fun state => cost.length-state.2.val)
    (fun state => state.2.val ≤ cost.length ∧ BestAmong state.1 (cutCandidates cost rows columns selectedRows selectedColumns state.2.val))
    _ _ _ ?_ (by simp only [UScalar.ofNatCore_val_eq,cutCandidates_zero]; exact ⟨Nat.zero_le _,bestAmong_self none⟩)
  rintro ⟨best,row⟩ ⟨hbound,hBest⟩
  dsimp only at hbound hBest ⊢
  unfold sparse.minimum_sparse_cut_loop.body
  dsimp only
  split
  · rename_i hlt
    have hb : row.val < cost.length := by scalar_tac
    have hSelBound : row.val < selectedRows.length := by rw [h.selected_rows_len]; exact hb
    apply WP.spec_bind (Slice.index_usize_spec selectedRows row hSelBound)
    intro bit hBit
    have hbit : selectedRows.val[row.val]! = bit := by
      simpa only [getElem!_pos selectedRows.val row.val hSelBound] using hBit.symm
    cases bit with
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      have hEmpty : matrixRow cost rows columns selectedRows selectedColumns row.val = [] := by
        simp only [matrixRow,hbit,Bool.false_eq_true,↓reduceIte]
      have hNextBest : BestAmong best (cutCandidates cost rows columns selectedRows selectedColumns (row.val+1)) := by
        rw [cutCandidates_succ,hEmpty,List.append_nil]
        exact hBest
      apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
      have he : next.val = row.val+1 := by simpa using hNext
      simpa only [he] using hNextBest
    | true =>
      simp only [↓reduceIte]
      apply WP.spec_bind (Slice.index_usize_spec cost row hb)
      intro inputRow hInputRow
      have hinput : inputRow = cost.val[row.val]! := by simpa only [getElem!_pos cost.val row.val hb] using hInputRow
      have hRowLen : inputRow.length = cost.length := by rw [hinput]; exact h.square row.val hb
      have hDerefLen : (alloc.vec.Vec.deref inputRow).length = cost.length := by
        simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length] using hRowLen
      have hPotBound : row.val < rows.length := by rw [h.rows_len]; exact hb
      apply WP.spec_bind (Slice.index_usize_spec rows row hPotBound)
      intro potential hPotential
      have hpotential : potential = rows.val[row.val]! := by simpa only [getElem!_pos rows.val row.val hPotBound] using hPotential
      apply WP.spec_bind (minimum_sparse_row_spec (alloc.vec.Vec.deref inputRow) potential columns selectedColumns row best
        (by rw [hDerefLen,h.columns_len]) (by rw [hDerefLen,h.selected_columns_len])
        (by rw [hpotential]; exact h.rows_bound row.val hb)
        (by intro index hi; exact h.columns_bound index (by omega)))
      rintro rowResult ⟨newBest,hRowResult,hRowBest⟩
      subst rowResult
      have hFrameRow : BestAmong newBest (bestEntries best++matrixRow cost rows columns selectedRows selectedColumns row.val) := by
        simpa only [matrixRow,hbit,↓reduceIte,hinput,hpotential,alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length] using hRowBest
      have hNextBest : BestAmong newBest (cutCandidates cost rows columns selectedRows selectedColumns (row.val+1)) := by
        rw [cutCandidates_succ]
        exact BestAmong.replace_frame hBest hFrameRow
      apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
      have he : next.val = row.val+1 := by simpa using hNext
      simpa only [he] using hNextBest
  · rename_i hnot
    simp only [WP.spec_ok]
    refine ⟨best,rfl,?_⟩
    have he : row.val = cost.length := by scalar_tac
    simpa only [he] using hBest

/-- Under the actual sparse state frame, the complete public Rust cut primitive
terminates safely with the exact independent minimum and an original attaining
edge, or none precisely when there are no candidates. -/
theorem minimum_sparse_cut_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (h : Input cost rows columns selectedRows selectedColumns) :
    sparse.minimum_sparse_cut cost rows columns selectedRows selectedColumns ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ BestAmong output (cutCandidates cost rows columns selectedRows selectedColumns cost.length) ⦄ := by
  have hr : Slice.len rows = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using h.rows_len)
  have hc : Slice.len columns = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using h.columns_len)
  have hsr : Slice.len selectedRows = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using h.selected_rows_len)
  have hsc : Slice.len selectedColumns = Slice.len cost := UScalar.eq_of_val_eq (by simpa only [Slice.len_val] using h.selected_columns_len)
  unfold sparse.minimum_sparse_cut
  simp only [hr,hc,hsr,hsc,bne_self_eq_false,Bool.false_eq_true,↓reduceIte]
  apply WP.spec_bind (square_shape_spec cost)
  intro valid hValid
  have hv : valid = true := hValid.mpr h.square
  subst valid
  simp only [↓reduceIte]
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX AssignmentEntrypoint.u32_max_fits_usize)
  intro limit hLimit
  have hl : limit.val = U32.max := hLimit.trans AssignmentEntrypoint.u32_max_value
  have hn : ¬ Slice.len cost > limit := by have hv := Slice.len_val cost; have hs := h.size; scalar_tac
  simp only [hn,↓reduceIte]
  exact minimum_sparse_cut_loop_spec cost rows columns selectedRows selectedColumns (Slice.len cost) (Slice.len_val cost) h

end SubtreeProofs.Rust.SparseCut

end
