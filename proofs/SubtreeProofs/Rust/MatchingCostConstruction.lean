module

public import SubtreeProofs.Rust.MatchingCostSpecification
import Mathlib.Tactic

/-!
# Actual construction of the partial-matching dummy cost matrix

The actual cell helper safely realizes the independent integer cost. Both
owned-vector push loops terminate with exact row/matrix contents; indexing,
subtraction, negation, cursor increments and modeled vector sizes are safe.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingCostConstruction

open MatchingCostSpecification

structure Dimensions (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize) : Prop where
  left_len : weights.length = left.val
  dimension_eq : dimension.val = left.val+right.val
  rectangular : ∀ row ∈ weights.val, row.length = right.val

theorem Dimensions.row_length (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize)
    (h : Dimensions weights left right dimension) (row : Nat) (hr : row < left.val) : (weights.val[row]!).length = right.val := by
  have hb : row < weights.length := by rw [h.left_len]; exact hr
  apply h.rectangular
  rw [getElem!_pos weights.val row hb]
  exact List.getElem_mem hb

/-- Every actual real or dummy cell equals the independent signed cost. -/
theorem cost_cell_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension row column : Usize)
    (dims : Dimensions weights left right dimension) (hc : column.val < dimension.val) :
    matching.cost_cell weights left row column ⦃ result => result.val = costAt weights left.val row.val column.val ⦄ := by
  have hd := dims.dimension_eq
  unfold matching.cost_cell
  split
  · rename_i hr
    have hrVal : row.val < left.val := by scalar_tac
    split
    · rename_i hcol
      have hcolVal : left.val ≤ column.val := by scalar_tac
      have hrowBound : row.val < weights.length := by rw [dims.left_len]; exact hrVal
      apply WP.spec_bind (Slice.index_usize_spec weights row hrowBound)
      intro inputRow hInputRow
      have hrow : inputRow = weights.val[row.val]! := by
        simpa only [getElem!_pos weights.val row.val hrowBound] using hInputRow
      apply WP.spec_bind (Usize.sub_spec (x := column) (y := left) (by scalar_tac))
      intro target hTarget
      have htarget : target.val = column.val-left.val := hTarget.1
      have hbound : target.val < inputRow.length := by
        rw [hrow,dims.row_length weights left right dimension row.val hrVal]
        omega
      simp only [alloc.vec.Vec.index_slice_index]
      apply WP.spec_bind (alloc.vec.Vec.index_usize_spec inputRow target hbound)
      intro value hValue
      have hvalue : value = (weights.val[row.val]!).val[column.val-left.val]! := by
        have hv : value = inputRow.val[target.val]! := by
          simpa only [getElem!_pos inputRow.val target.val hbound] using hValue
        simpa only [hrow,htarget] using hv
      apply WP.spec_mono (negative_profit_spec value)
      intro result hresult
      simpa only [costAt,hrVal,hcolVal,and_self,↓reduceIte,hvalue] using hresult
    · rename_i hcol
      have hn : ¬ left.val ≤ column.val := by scalar_tac
      simp only [WP.spec_ok,costAt,hn,and_false,↓reduceIte,IScalar.ofInt_val_eq]
  · rename_i hr
    have hn : ¬ row.val < left.val := by scalar_tac
    simp only [WP.spec_ok,costAt,hn,false_and,↓reduceIte,IScalar.ofInt_val_eq]

def rowValues (weights : Slice (alloc.vec.Vec (Option I64))) (left row width : Nat) : List ℤ :=
  (List.range width).map (costAt weights left row)

@[simp] theorem rowValues_length (weights : Slice (alloc.vec.Vec (Option I64))) (left row width : Nat) :
    (rowValues weights left row width).length = width := by simp [rowValues]

theorem rowValues_succ (weights : Slice (alloc.vec.Vec (Option I64))) (left row width : Nat) :
    rowValues weights left row (width+1) = rowValues weights left row width ++ [costAt weights left row width] := by
  simp only [rowValues,List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-- The complete actual owned-row loop safely builds exactly the specified
integer dummy-cost row, retaining every physical slot through its value view. -/
theorem cost_row_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension row : Usize)
    (dims : Dimensions weights left right dimension) :
    matching.cost_row weights left dimension row ⦃ result => result.val.map IScalar.val = rowValues weights left.val row.val dimension.val ⦄ := by
  unfold matching.cost_row matching.cost_row_loop
  apply loop.spec_decr_nat (fun (state : alloc.vec.Vec I64 × Usize) => dimension.val-state.2.val)
    (fun (state : alloc.vec.Vec I64 × Usize) => state.2.val ≤ dimension.val ∧ state.1.val.map IScalar.val = rowValues weights left.val row.val state.2.val)
    (fun (result : alloc.vec.Vec I64) => result.val.map IScalar.val = rowValues weights left.val row.val dimension.val) _ _ ?_ (by simp [rowValues])
  rintro ⟨result,column⟩ ⟨hcolumn,hvalues⟩
  dsimp only at hcolumn hvalues ⊢
  unfold matching.cost_row_loop.body
  split
  · rename_i hc
    have hcol : column.val < dimension.val := by scalar_tac
    have hlen : result.length = column.val := by
      have h := congrArg List.length hvalues
      simpa only [List.length_map,rowValues_length] using h
    apply WP.spec_bind (cost_cell_spec weights left right dimension row column dims hcol)
    intro value hValue
    apply WP.spec_bind (alloc.vec.Vec.push_spec result value (by change result.length < Usize.max; rw [hlen]; scalar_tac))
    intro nextResult hResult
    apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
    intro next hNext
    have hnext : next.val = column.val+1 := by simpa using hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by omega,?_⟩,by omega⟩
    rw [hResult,List.map_append,List.map_cons,List.map_nil,hvalues,hValue,hnext,rowValues_succ]
  · rename_i hc
    have he : column.val = dimension.val := by scalar_tac
    simp only [WP.spec_ok]
    simpa only [he] using hvalues

def matrixValues (weights : Slice (alloc.vec.Vec (Option I64))) (left width count : Nat) : List (List ℤ) :=
  (List.range count).map (fun row => rowValues weights left row width)

@[simp] theorem matrixValues_length (weights : Slice (alloc.vec.Vec (Option I64))) (left width count : Nat) :
    (matrixValues weights left width count).length = count := by simp [matrixValues]

theorem matrixValues_succ (weights : Slice (alloc.vec.Vec (Option I64))) (left width count : Nat) :
    matrixValues weights left width (count+1) = matrixValues weights left width count ++ [rowValues weights left count width] := by
  simp only [matrixValues,List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-- The complete actual matrix loop safely constructs all real and dummy
rows, with exact contents against the independent reduction cost model. -/
theorem cost_matrix_spec (weights : Slice (alloc.vec.Vec (Option I64))) (left right dimension : Usize)
    (dims : Dimensions weights left right dimension) :
    matching.cost_matrix weights left dimension ⦃ result =>
      result.val.map (fun row => row.val.map IScalar.val) = matrixValues weights left.val dimension.val dimension.val ⦄ := by
  unfold matching.cost_matrix matching.cost_matrix_loop
  apply loop.spec_decr_nat (fun (state : alloc.vec.Vec (alloc.vec.Vec I64) × Usize) => dimension.val-state.2.val)
    (fun (state : alloc.vec.Vec (alloc.vec.Vec I64) × Usize) => state.2.val ≤ dimension.val ∧
      state.1.val.map (fun row => row.val.map IScalar.val) = matrixValues weights left.val dimension.val state.2.val)
    (fun (result : alloc.vec.Vec (alloc.vec.Vec I64)) => result.val.map (fun row => row.val.map IScalar.val) = matrixValues weights left.val dimension.val dimension.val) _ _ ?_
    (by simp [matrixValues])
  rintro ⟨result,row⟩ ⟨hrow,hvalues⟩
  dsimp only at hrow hvalues ⊢
  unfold matching.cost_matrix_loop.body
  split
  · rename_i hr
    have hlen : result.length = row.val := by
      have h := congrArg List.length hvalues
      simpa only [List.length_map,matrixValues_length] using h
    apply WP.spec_bind (cost_row_spec weights left right dimension row dims)
    intro newRow hNewRow
    apply WP.spec_bind (alloc.vec.Vec.push_spec result newRow (by change result.length < Usize.max; rw [hlen]; scalar_tac))
    intro nextResult hResult
    apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
    intro next hNext
    have hnext : next.val = row.val+1 := by simpa using hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
    rw [hResult,List.map_append,List.map_cons,List.map_nil,hvalues,hNewRow,hnext,matrixValues_succ]
  · rename_i hr
    have he : row.val = dimension.val := by scalar_tac
    simp only [WP.spec_ok]
    simpa only [he] using hvalues

end SubtreeProofs.Rust.MatchingCostConstruction

end
