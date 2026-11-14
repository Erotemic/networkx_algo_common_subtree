module

public import SubtreeProofs.Rust.SparseDeletionProjection
import Mathlib.Tactic

/-! # Actual sparse-deletion bypass completion and coordinate compression -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

/-- The source selects the bypass column at the free row and otherwise keeps
that row's old original assignment column. -/
def selectedColumn (completed : Slice Usize) (freeRow freeColumn row : Usize) : Usize :=
  if row = freeRow then freeColumn else completed.val[row.val]!

def compressedValue (column removed : Usize) : Nat :=
  if column.val < removed.val then column.val else column.val-1

theorem selected_column_spec (completed : Slice Usize) (freeRow freeColumn row : Usize)
    (hRow : row.val < completed.length) :
    (if row = freeRow then ok freeColumn else Slice.index_usize completed row) ⦃ column =>
      column = selectedColumn completed freeRow freeColumn row ⦄ := by
  by_cases he : row = freeRow
  · simp only [he,↓reduceIte,selectedColumn,WP.spec_ok]
  · simp only [he,↓reduceIte,selectedColumn]
    apply WP.spec_mono (Slice.index_usize_spec completed row hRow)
    intro column hColumn
    simpa only [getElem!_pos completed.val row.val hRow] using hColumn

/-- Every successful source compression appends exactly one compact column;
the survivor and no-deleted-column premises will be discharged by the
independent finite permutation bridge, not by an assumed source success. -/
theorem complete_surviving_loop_spec (completed vertices : Slice Usize)
    (removed freeRow freeColumn : Usize)
    (hRows : ∀ row ∈ vertices.val, row.val < completed.length)
    (hSurvives : ∀ row ∈ vertices.val, selectedColumn completed freeRow freeColumn row ≠ removed) :
    sparse_deletion.complete_surviving_loop completed vertices removed freeRow freeColumn
      (alloc.vec.Vec.new Usize) 0#usize none ⦃ result =>
      result.2 = none ∧ result.1.val.map UScalar.val = vertices.val.map (fun row =>
        compressedValue (selectedColumn completed freeRow freeColumn row) removed) ⦄ := by
  unfold sparse_deletion.complete_surviving_loop
  apply loop.spec_decr_nat (fun state => vertices.length-state.2.1.val)
    (fun state => state.2.2 = none ∧ state.2.1.val ≤ vertices.length ∧
      state.1.val.map UScalar.val = (vertices.val.take state.2.1.val).map (fun row =>
        compressedValue (selectedColumn completed freeRow freeColumn row) removed))
    _ _ _ ?_ (by simp)
  rintro ⟨result,index,failure⟩ ⟨rfl,hIndex,hPrefix⟩
  dsimp only at hIndex hPrefix ⊢
  unfold sparse_deletion.complete_surviving_loop.body
  dsimp only
  split
  · rename_i hlt
    have hLen := Slice.len_val vertices
    have hi : index.val < vertices.length := by scalar_tac
    simp only [core.option.Option.is_none]
    apply WP.spec_bind (Slice.index_usize_spec vertices index hi)
    intro row hRow
    have hm : row ∈ vertices.val := by rw [hRow]; exact List.getElem_mem hi
    apply WP.spec_bind (selected_column_spec completed freeRow freeColumn row (hRows row hm))
    intro column hColumn
    have hNe : column ≠ removed := by rw [hColumn]; exact hSurvives row hm
    apply WP.spec_bind (compact_index_total_spec column removed)
    intro compact hCompact
    rw [ite_eq_right hNe] at hCompact
    obtain ⟨value,rfl,hValue⟩ := hCompact
    simp only [Std.bind_assoc]
    have hResultLength : result.val.length = index.val := by
      have h := congrArg List.length hPrefix
      simpa only [List.length_map,List.length_take,Nat.min_eq_left hIndex] using h
    apply WP.spec_bind (alloc.vec.Vec.push_spec result value (by rw [hResultLength]; scalar_tac))
    intro updated hUpdated
    simp only [bind_ok,uncurry_apply_pair]
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro next hNext
    simp only [WP.spec_ok]
    refine ⟨⟨True.intro,by scalar_tac,?_⟩,by scalar_tac⟩
    have hn : next.val = index.val+1 := by scalar_tac
    rw [hUpdated,List.map_append,List.map_singleton,hPrefix,hn,
      List.take_succ_eq_append_getElem hi,List.map_append,List.map_singleton]
    have hc : value.val = compressedValue (selectedColumn completed freeRow freeColumn row) removed := by
      simpa only [compressedValue,hColumn] using hValue
    rw [hc,hRow]
  · rename_i hnot
    have he : index.val = vertices.length := by have hl := Slice.len_val vertices; scalar_tac
    exact (WP.spec_ok _).mpr ⟨rfl,by simpa only [he,List.take_length] using hPrefix⟩

theorem complete_surviving_spec (completed vertices : Slice Usize)
    (removed freeRow freeColumn : Usize)
    (hRows : ∀ row ∈ vertices.val, row.val < completed.length)
    (hSurvives : ∀ row ∈ vertices.val, selectedColumn completed freeRow freeColumn row ≠ removed) :
    sparse_deletion.complete_surviving completed vertices removed freeRow freeColumn ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ output.val.map UScalar.val = vertices.val.map (fun row =>
        compressedValue (selectedColumn completed freeRow freeColumn row) removed) ⦄ := by
  unfold sparse_deletion.complete_surviving
  apply WP.spec_bind (complete_surviving_loop_spec completed vertices removed freeRow freeColumn hRows hSurvives)
  rintro ⟨output,failure⟩ ⟨rfl,hOutput⟩
  exact (WP.spec_ok _).mpr ⟨output,rfl,hOutput⟩

end SubtreeProofs.Rust.SparseDeletion

end
