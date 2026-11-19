module

public import SubtreeProofs.Rust.SparseCutEntrypoint
import Mathlib.Tactic

/-! # Original-edge meaning of independent sparse-cut candidate membership -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

/-- Exact absence of an attaining cut means there are no allowed candidates. -/
theorem BestAmong.none_iff {best : Option sparse.SparseCut} {candidates : List Entry} (h : BestAmong best candidates) :
    best = none ↔ candidates = [] := by
  constructor
  · intro he
    subst best
    have hn : candidates.map Prod.snd = [] := List.minimum_eq_top.mp h.1.symm
    have hl := congrArg List.length hn
    simp only [List.length_map,List.length_nil] at hl
    exact List.eq_nil_of_length_eq_zero hl
  · intro he
    cases best with
    | none => rfl
    | some cut =>
      have hv := h.1
      simp [he,toMinimum] at hv

/-- An attained independent minimum bounds every actual candidate value. -/
theorem BestAmong.bounds {cut : sparse.SparseCut} {candidates : List Entry} (h : BestAmong (some cut) candidates) :
    ∀ entry ∈ candidates, cut.delta.val ≤ entry.2 := by
  have hm := List.minimum_eq_coe_iff.mp h.1.symm
  intro entry he
  exact hm.2 entry.2 (List.mem_map.mpr ⟨entry,he,rfl⟩)

theorem mem_rowCandidates (cost : Slice (Option I64)) (potential : I128) (columns : Slice I128)
    (selected : Slice Bool) (row upto : Nat) (entry : Entry) :
    entry ∈ rowCandidates cost potential columns selected row upto ↔
      ∃ column, column < upto ∧ selected.val[column]! = false ∧ ∃ value,
        cost.val[column]! = some value ∧ entry = ((row,column),value.val-potential.val-columns.val[column]!.val) := by
  simp only [rowCandidates,List.mem_filterMap,List.mem_range]
  constructor
  · rintro ⟨column,hColumn,hEntry⟩
    unfold rowEntry at hEntry
    cases hFlag : selected.val[column]! with
    | true => simp only [hFlag,↓reduceIte,reduceCtorEq] at hEntry
    | false =>
      simp only [hFlag,Bool.false_eq_true,↓reduceIte] at hEntry
      cases hCost : cost.val[column]! with
      | none => simp only [hCost,Option.map_none,reduceCtorEq] at hEntry
      | some value =>
        have he : ((row,column),value.val-potential.val-columns.val[column]!.val) = entry :=
          Option.some.inj (by simpa only [hCost,Option.map_some] using hEntry)
        exact ⟨column,hColumn,hFlag,value,hCost,he.symm⟩
  · rintro ⟨column,hColumn,hFlag,value,hCost,rfl⟩
    exact ⟨column,hColumn,by simp only [rowEntry,hFlag,hCost,Bool.false_eq_true,↓reduceIte,Option.map_some]⟩

/-- An independently allowed original cut edge with its exact integer slack. -/
def OriginalEntry (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (entry : Entry) : Prop :=
  ∃ row, row < cost.length ∧ ∃ column, column < cost.length ∧
    selectedRows.val[row]! = true ∧ selectedColumns.val[column]! = false ∧
    ∃ value, cost.val[row]!.val[column]! = some value ∧
      entry = ((row,column),value.val-rows.val[row]!.val-columns.val[column]!.val)

/-- Full candidate membership is exactly an allowed selected-row/unselected-
column edge of the original optional matrix, with its original coordinates. -/
theorem mem_cutCandidates (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (h : Square cost) (entry : Entry) :
    entry ∈ cutCandidates cost rows columns selectedRows selectedColumns cost.length ↔
      OriginalEntry cost rows columns selectedRows selectedColumns entry := by
  simp only [cutCandidates,List.mem_flatMap,List.mem_range]
  constructor
  · rintro ⟨row,hRow,hEntry⟩
    unfold matrixRow at hEntry
    cases hFlag : selectedRows.val[row]! with
    | false => simp only [hFlag,Bool.false_eq_true,↓reduceIte,List.not_mem_nil] at hEntry
    | true =>
      simp only [hFlag,↓reduceIte] at hEntry
      obtain ⟨column,hColumn,hColumnFlag,value,hCost,hValue⟩ := (mem_rowCandidates _ _ _ _ _ _ _).mp hEntry
      refine ⟨row,hRow,column,?_,hFlag,hColumnFlag,value,?_,hValue⟩
      · exact hColumn.trans_le (le_of_eq (h row hRow))
      · simpa only [alloc.vec.Vec.deref,Slice.from_val] using hCost
  · rintro ⟨row,hRow,column,hColumn,hFlag,hColumnFlag,value,hCost,hValue⟩
    refine ⟨row,hRow,?_⟩
    simp only [matrixRow,hFlag,↓reduceIte]
    apply (mem_rowCandidates _ _ _ _ _ _ _).mpr
    refine ⟨column,?_,hColumnFlag,value,?_,hValue⟩
    · rw [h row hRow]
      exact hColumn
    · simpa only [alloc.vec.Vec.deref,Slice.from_val] using hCost

/-- Independent cut-answer contract on actual original matrix edges. Absence
means no allowed crossing edge; a returned record is an original attaining edge
whose reduced cost bounds every original allowed crossing edge. -/
def MinimumCut (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (output : Option sparse.SparseCut) : Prop :=
  match output with
  | none => ¬ ∃ entry, OriginalEntry cost rows columns selectedRows selectedColumns entry
  | some cut => OriginalEntry cost rows columns selectedRows selectedColumns (cutEntry cut) ∧
      ∀ entry, OriginalEntry cost rows columns selectedRows selectedColumns entry → cut.delta.val ≤ entry.2

/-- Candidate-list minima are exactly minima over original optional cut edges. -/
theorem bestAmong_minimumCut (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (hs : Square cost) (output : Option sparse.SparseCut)
    (h : BestAmong output (cutCandidates cost rows columns selectedRows selectedColumns cost.length)) :
    MinimumCut cost rows columns selectedRows selectedColumns output := by
  cases output with
  | none =>
    rintro ⟨entry,hEntry⟩
    have hm := (mem_cutCandidates cost rows columns selectedRows selectedColumns hs entry).mpr hEntry
    rw [h.none_iff.mp rfl] at hm
    exact List.not_mem_nil hm
  | some cut =>
    exact ⟨(mem_cutCandidates cost rows columns selectedRows selectedColumns hs _).mp (h.2 cut rfl),
      fun entry he => h.bounds entry ((mem_cutCandidates cost rows columns selectedRows selectedColumns hs entry).mpr he)⟩

/-- The actual whole Rust primitive returns precisely the independent minimum
of allowed original cut edges under its shape and bounded-potential frame. -/
theorem minimum_sparse_cut_edges_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (h : Input cost rows columns selectedRows selectedColumns) :
    sparse.minimum_sparse_cut cost rows columns selectedRows selectedColumns ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ MinimumCut cost rows columns selectedRows selectedColumns output ⦄ := by
  apply WP.spec_mono (minimum_sparse_cut_spec cost rows columns selectedRows selectedColumns h)
  rintro result ⟨output,hResult,hBest⟩
  exact ⟨output,hResult,bestAmong_minimumCut cost rows columns selectedRows selectedColumns h.square output hBest⟩

end SubtreeProofs.Rust.SparseCut

end
