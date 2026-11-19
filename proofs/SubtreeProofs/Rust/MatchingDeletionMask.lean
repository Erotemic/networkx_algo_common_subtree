module

public import SubtreeProofs.Rust.MatchingCostConstruction
import Mathlib.Tactic

/-! # Actual original-index-preserving construction of a deleted-column matrix -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.MatchingDeletionMask

def maskAt (row : List (Option I64)) (removed column : Nat) : Option I64 :=
  if column = removed then none else row[column]!

def rowPrefix (row : List (Option I64)) (removed count : Nat) : List (Option I64) :=
  (List.range count).map (maskAt row removed)

@[simp] theorem rowPrefix_length (row : List (Option I64)) (removed count : Nat) :
    (rowPrefix row removed count).length = count := by simp [rowPrefix]

theorem rowPrefix_succ (row : List (Option I64)) (removed count : Nat) :
    rowPrefix row removed (count+1) = rowPrefix row removed count ++ [maskAt row removed count] := by
  simp only [rowPrefix,List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-- The complete actual row mask safely preserves every other input entry and
its original column index, including empty rows and absent removed columns. -/
theorem mask_row_spec (row : Slice (Option I64)) (removed : Usize) :
    deletion.mask_row row removed ⦃ result => result.val = rowPrefix row.val removed.val row.length ⦄ := by
  unfold deletion.mask_row deletion.mask_row_loop
  apply loop.spec_decr_nat
    (fun (state : alloc.vec.Vec (Option I64) × Usize) => row.length-state.2.val)
    (fun (state : alloc.vec.Vec (Option I64) × Usize) => state.2.val ≤ row.length ∧
      state.1.val = rowPrefix row.val removed.val state.2.val)
    (fun (result : alloc.vec.Vec (Option I64)) => result.val = rowPrefix row.val removed.val row.length)
    _ _ ?_ (by simp [rowPrefix])
  rintro ⟨result,column⟩ ⟨hcolumn,hprefix⟩
  dsimp only at hcolumn hprefix ⊢
  have hlen := Slice.len_val row
  have hc : result.length = column.val := by
    change result.val.length = column.val
    rw [hprefix,rowPrefix_length]
  unfold deletion.mask_row_loop.body
  dsimp only
  split
  · rename_i hi
    have hp : column.val < row.length := by scalar_tac
    have hcell : (if column = removed then alloc.vec.Vec.push result none else do
        let entry ← Slice.index_usize row column
        alloc.vec.Vec.push result entry) ⦃ next =>
          next.val = result.val ++ [maskAt row.val removed.val column.val] ⦄ := by
      split
      · rename_i he
        subst column
        have hpush := alloc.vec.Vec.push_spec result none (by scalar_tac)
        simpa only [maskAt,↓reduceIte] using hpush
      · rename_i hn
        have hne : column.val ≠ removed.val := by intro he; exact hn (UScalar.eq_of_val_eq he)
        apply WP.spec_bind (Slice.index_usize_spec row column hp)
        intro entry hEntry
        apply WP.spec_mono (alloc.vec.Vec.push_spec result entry (by scalar_tac))
        intro next hNext
        simpa only [maskAt,hne,↓reduceIte,getElem!_pos row.val column.val hp,hEntry] using hNext
    apply WP.spec_bind hcell
    intro nextResult hNextResult
    apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
    intro next hNext
    have hn : next.val = column.val+1 := by simpa using hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by omega,?_⟩,by omega⟩
    rw [hNextResult,hprefix,hn,rowPrefix_succ]
  · rename_i hi
    have he : column.val = row.length := by scalar_tac
    simp only [WP.spec_ok]
    simpa only [he] using hprefix

def matrixPrefix (weights : Slice (alloc.vec.Vec (Option I64))) (removed count : Nat) : List (List (Option I64)) :=
  (weights.val.take count).map (fun row => rowPrefix row.val removed row.length)

/-- Both actual owned-vector construction loops are safe and have exact
original-index-preserving optional-weight contents. -/
theorem mask_right_spec (weights : Slice (alloc.vec.Vec (Option I64))) (removed : Usize) :
    deletion.mask_right weights removed ⦃ result => result.val.map alloc.vec.Vec.val =
      matrixPrefix weights removed.val weights.length ⦄ := by
  unfold deletion.mask_right deletion.mask_right_loop
  apply loop.spec_decr_nat
    (fun (state : alloc.vec.Vec (alloc.vec.Vec (Option I64)) × Usize) => weights.length-state.2.val)
    (fun (state : alloc.vec.Vec (alloc.vec.Vec (Option I64)) × Usize) => state.2.val ≤ weights.length ∧
      state.1.val.map alloc.vec.Vec.val = matrixPrefix weights removed.val state.2.val)
    (fun (result : alloc.vec.Vec (alloc.vec.Vec (Option I64))) => result.val.map alloc.vec.Vec.val =
      matrixPrefix weights removed.val weights.length)
    _ _ ?_ (by simp [matrixPrefix])
  rintro ⟨result,row⟩ ⟨hrow,hprefix⟩
  dsimp only at hrow hprefix ⊢
  have hlen := Slice.len_val weights
  have hc : result.length = row.val := by
    have he := congrArg List.length hprefix
    simpa only [matrixPrefix,List.length_map,List.length_take,Nat.min_eq_left hrow] using he
  unfold deletion.mask_right_loop.body
  dsimp only
  split
  · rename_i hi
    have hp : row.val < weights.length := by scalar_tac
    apply WP.spec_bind (Slice.index_usize_spec weights row hp)
    intro inputRow hInputRow
    apply WP.spec_bind (mask_row_spec (alloc.vec.Vec.deref inputRow) removed)
    intro maskedRow hMaskedRow
    apply WP.spec_bind (alloc.vec.Vec.push_spec result maskedRow (by scalar_tac))
    intro nextResult hNextResult
    apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
    intro next hNext
    have hn : next.val = row.val+1 := by simpa using hNext
    simp only [WP.spec_ok]
    refine ⟨⟨by omega,?_⟩,by omega⟩
    rw [hNextResult,List.map_append,List.map_cons,List.map_nil,hprefix,hn]
    simp only [matrixPrefix,List.take_succ_eq_append_getElem hp,List.map_append,List.map_cons,List.map_nil]
    rw [hMaskedRow,hInputRow]
    simp only [alloc.vec.Vec.deref,Slice.from_val,Slice.length,alloc.vec.Vec.length]
  · rename_i hi
    have he : row.val = weights.length := by scalar_tac
    simp only [WP.spec_ok]
    simpa only [he] using hprefix

end SubtreeProofs.Rust.MatchingDeletionMask

end
