module

public import SubtreeProofs.Rust.SparseCutRowSpecification
import Mathlib.Tactic

/-! # Actual sparse row scan: exact attained minimum and checked arithmetic -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

/-- The actual row scan safely appends all allowed row candidates to its
initial minimum frame. Length and uniform potential bounds discharge every
source read, cast, checked subtraction and counter increment. -/
theorem minimum_sparse_row_spec (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row : Usize) (initial : Option sparse.SparseCut)
    (hc : cost.length ≤ columns.length) (hs : cost.length ≤ selected.length)
    (hp : -potentialBound ≤ potential.val ∧ potential.val ≤ potentialBound)
    (hcolumns : ∀ index, index < cost.length → -potentialBound ≤ columns.val[index]!.val ∧ columns.val[index]!.val ≤ potentialBound) :
    sparse.minimum_sparse_row cost potential columns selected row initial ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧
      BestAmong output (bestEntries initial++rowCandidates cost potential columns selected row.val cost.length) ⦄ := by
  unfold sparse.minimum_sparse_row sparse.minimum_sparse_row_loop
  apply loop.spec_decr_nat (fun state => cost.length-state.2.val)
    (fun state => state.2.val ≤ cost.length ∧
      BestAmong state.1 (bestEntries initial++rowCandidates cost potential columns selected row.val state.2.val))
    _ _ _ ?_ (by simpa only [UScalar.ofNatCore_val_eq,rowCandidates_zero,List.append_nil] using And.intro (Nat.zero_le cost.length) (bestAmong_self initial))
  rintro ⟨best,column⟩ ⟨hbound,hBest⟩
  dsimp only at hbound hBest ⊢
  unfold sparse.minimum_sparse_row_loop.body
  dsimp only
  have hlen := Slice.len_val cost
  split
  · rename_i hlt
    have hb : column.val < cost.length := by scalar_tac
    have hSelBound : column.val < selected.length := by omega
    apply WP.spec_bind (Slice.index_usize_spec selected column hSelBound)
    intro bit hBit
    have hbit : selected.val[column.val]! = bit := by
      simpa only [getElem!_pos selected.val column.val hSelBound] using hBit.symm
    cases bit with
    | true =>
      simp only [↓reduceIte]
      have hEntry : rowEntry cost potential columns selected row.val column.val = none := by simp only [rowEntry,hbit,↓reduceIte]
      have hNextBest : BestAmong best (bestEntries initial++rowCandidates cost potential columns selected row.val (column.val+1)) := by
        rw [rowCandidates_succ,hEntry]
        simpa only [Option.toList_none,List.append_nil] using hBest
      apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
      intro next hNext
      simp only [WP.spec_ok]
      refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
      have he : next.val = column.val+1 := by simpa using hNext
      simpa only [he] using hNextBest
    | false =>
      simp only [Bool.false_eq_true,↓reduceIte]
      apply WP.spec_bind (Slice.index_usize_spec cost column hb)
      intro edge hEdge
      have hedge : cost.val[column.val]! = edge := by
        simpa only [getElem!_pos cost.val column.val hb] using hEdge.symm
      cases edge with
      | none =>
        have hEntry : rowEntry cost potential columns selected row.val column.val = none := by
          simp only [rowEntry,hbit,hedge,Bool.false_eq_true,↓reduceIte,Option.map_none]
        have hNextBest : BestAmong best (bestEntries initial++rowCandidates cost potential columns selected row.val (column.val+1)) := by
          rw [rowCandidates_succ,hEntry]
          simpa only [Option.toList_none,List.append_nil] using hBest
        apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
        intro next hNext
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
        have he : next.val = column.val+1 := by simpa using hNext
        simpa only [he] using hNextBest
      | some value =>
        apply WP.spec_bind (IScalar.cast_inBounds_spec .I128 value (by scalar_tac))
        intro widened hWidened
        have hpBound := hp
        norm_num [potentialBound] at hpBound
        apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec widened potential (by scalar_tac) (by scalar_tac))
        rintro firstOption ⟨first,hFirstOption,hFirst⟩
        subst firstOption
        have hColBound : column.val < columns.length := by omega
        apply WP.spec_bind (Slice.index_usize_spec columns column hColBound)
        intro columnValue hColumnValue
        have hcv : columns.val[column.val]!.val = columnValue.val := by
          simpa only [getElem!_pos columns.val column.val hColBound] using (congrArg IScalar.val hColumnValue).symm
        have hcvBound := hcolumns column.val hb
        rw [hcv] at hcvBound
        norm_num [potentialBound] at hcvBound
        apply WP.spec_bind (AssignmentArithmetic.checked_sub_spec first columnValue (by scalar_tac) (by scalar_tac))
        rintro deltaOption ⟨delta,hDeltaOption,hDelta⟩
        subst deltaOption
        let candidate : sparse.SparseCut := ⟨row,column,delta⟩
        have hEntry : rowEntry cost potential columns selected row.val column.val = some (cutEntry candidate) := by
          simp only [rowEntry,hbit,hedge,Bool.false_eq_true,↓reduceIte,Option.map_some,cutEntry,candidate,hDelta,hFirst,hWidened,hcv]
        apply WP.spec_bind (select_cut_best_spec best candidate
          (bestEntries initial++rowCandidates cost potential columns selected row.val column.val) hBest)
        intro chosen hChosen
        have hNextBest : BestAmong (some chosen) (bestEntries initial++rowCandidates cost potential columns selected row.val (column.val+1)) := by
          rw [rowCandidates_succ,hEntry]
          simpa only [Option.toList_some,List.append_assoc] using hChosen
        apply WP.spec_bind (Usize.add_spec (x := column) (y := 1#usize) (by scalar_tac))
        intro next hNext
        simp only [WP.spec_ok]
        refine ⟨⟨by scalar_tac,?_⟩,by scalar_tac⟩
        have he : next.val = column.val+1 := by simpa using hNext
        simpa only [he] using hNextBest
  · rename_i hn
    simp only [WP.spec_ok]
    refine ⟨best,rfl,?_⟩
    have he : column.val = cost.length := by scalar_tac
    simpa only [he] using hBest

end SubtreeProofs.Rust.SparseCut

end
