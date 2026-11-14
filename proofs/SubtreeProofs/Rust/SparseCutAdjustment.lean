module

public import SubtreeProofs.Rust.SparseCutCandidates
public import SubtreeProofs.Shared.AssignmentSparsePotentials
import Mathlib.Tactic

/-! # Actual sparse cut output supplies an allowed tight-edge dual adjustment -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseCut

abbrev Vertex (cost : Slice (alloc.vec.Vec (Option I64))) := Fin cost.length

def allowed (cost : Slice (alloc.vec.Vec (Option I64))) (row column : Vertex cost) : Prop :=
  cost.val[row.val]!.val[column.val]! ≠ none

def matrix (cost : Slice (alloc.vec.Vec (Option I64))) (row column : Vertex cost) : ℤ :=
  ((cost.val[row.val]!.val[column.val]!).map IScalar.val).getD 0

def potentialAt (cost : Slice (alloc.vec.Vec (Option I64))) (values : Slice I128) (vertex : Vertex cost) : ℤ :=
  values.val[vertex.val]!.val

/-- The independently selected graph vertices represented by source flags. -/
def chosen (cost : Slice (alloc.vec.Vec (Option I64))) (flags : Slice Bool) : Finset (Vertex cost) :=
  Finset.univ.filter (fun vertex => flags.val[vertex.val]!)

@[simp] theorem mem_chosen (cost : Slice (alloc.vec.Vec (Option I64))) (flags : Slice Bool) (vertex : Vertex cost) :
    vertex ∈ chosen cost flags ↔ flags.val[vertex.val]! = true := by simp only [chosen,Finset.mem_filter,Finset.mem_univ,true_and]

theorem matrix_at_some (cost : Slice (alloc.vec.Vec (Option I64))) (row column : Vertex cost) (value : I64)
    (h : cost.val[row.val]!.val[column.val]! = some value) : matrix cost row column = value.val := by
  simp only [matrix,h,Option.map_some,Option.getD_some]

/-- A one-excess-row cut in a graph admitting a compatible perfect assignment
contains an actual original matrix edge. This rules out the source's absent-cut
result under the independent alternating-search conditions. -/
theorem originalEntry_exists (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool)
    (hcard : (chosen cost selectedRows).card = (chosen cost selectedColumns).card+1)
    (he : ∃ assignment : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) assignment) :
    ∃ entry, OriginalEntry cost rows columns selectedRows selectedColumns entry := by
  obtain ⟨assignment,hAssignment⟩ := he
  obtain ⟨row,hRow,column,hColumn,hEdge⟩ := Assignment.exists_allowed_crossing (allowed cost) assignment hAssignment
    (chosen cost selectedRows) (chosen cost selectedColumns) (by omega)
  have hr : selectedRows.val[row.val]! = true := (mem_chosen cost selectedRows row).mp hRow
  have hc : selectedColumns.val[column.val]! = false := by
    cases hFlag : selectedColumns.val[column.val]! with
    | false => rfl
    | true => exact False.elim (hColumn ((mem_chosen cost selectedColumns column).mpr hFlag))
  obtain ⟨value,hValue⟩ := Option.ne_none_iff_exists'.mp hEdge
  exact ⟨((row.val,column.val),value.val-rows.val[row.val]!.val-columns.val[column.val]!.val),
    row.val,row.isLt,column.val,column.isLt,hr,hc,value,hValue,rfl⟩

/-- Exact original endpoints, an actual allowed tight edge after the ideal
update, and preservation of sparse dual feasibility. The Rust primitive returns
the adjustment; physical potential-vector updating is a separate source step. -/
def Adjustment (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (cut : sparse.SparseCut) : Prop :=
  ∃ row column : Vertex cost,
    row.val = cut.row.val ∧ column.val = cut.column.val ∧
    row ∈ chosen cost selectedRows ∧ column ∉ chosen cost selectedColumns ∧ allowed cost row column ∧
    cut.delta.val = matrix cost row column-potentialAt cost rows row-potentialAt cost columns column ∧ 0 ≤ cut.delta.val ∧
    Assignment.FeasibleOn (allowed cost) (matrix cost)
      (Assignment.adjustRows (potentialAt cost rows) (chosen cost selectedRows) cut.delta.val)
      (Assignment.adjustColumns (potentialAt cost columns) (chosen cost selectedColumns) cut.delta.val) ∧
    Assignment.adjustRows (potentialAt cost rows) (chosen cost selectedRows) cut.delta.val row+
      Assignment.adjustColumns (potentialAt cost columns) (chosen cost selectedColumns) cut.delta.val column = matrix cost row column

/-- An independent minimum original cut edge yields exactly the sparse dual
update justified by the mathematical cut theorem. -/
theorem minimumCut_adjustment (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (cut : sparse.SparseCut)
    (h : MinimumCut cost rows columns selectedRows selectedColumns (some cut))
    (hf : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost rows) (potentialAt cost columns)) :
    Adjustment cost rows columns selectedRows selectedColumns cut := by
  obtain ⟨r,hr,c,hc,hSelected,hUnselected,value,hValue,hEntry⟩ := h.1
  let row : Vertex cost := ⟨r,hr⟩
  let column : Vertex cost := ⟨c,hc⟩
  have hrow : row.val = cut.row.val := (congrArg (fun entry : Entry => entry.1.1) hEntry).symm
  have hcolumn : column.val = cut.column.val := (congrArg (fun entry : Entry => entry.1.2) hEntry).symm
  have hAllowed : allowed cost row column := by simp only [allowed,row,column,hValue,ne_eq,reduceCtorEq,not_false_eq_true]
  have hDelta : cut.delta.val = matrix cost row column-potentialAt cost rows row-potentialAt cost columns column := by
    rw [matrix_at_some cost row column value hValue]
    exact congrArg Prod.snd hEntry
  have hRow : row ∈ chosen cost selectedRows := (mem_chosen cost selectedRows row).mpr hSelected
  have hColumn : column ∉ chosen cost selectedColumns := by
    rw [mem_chosen,hUnselected]
    decide
  have hNonnegative : 0 ≤ cut.delta.val := by
    have hb := hf row column hAllowed
    rw [hDelta]
    linarith
  have hCut : ∀ first ∈ chosen cost selectedRows, ∀ second, second ∉ chosen cost selectedColumns → allowed cost first second →
      cut.delta.val ≤ matrix cost first second-potentialAt cost rows first-potentialAt cost columns second := by
    intro first hFirst second hSecond hEdge
    have hFirstFlag := (mem_chosen cost selectedRows first).mp hFirst
    have hSecondFlag : selectedColumns.val[second.val]! = false := by
      cases hFlag : selectedColumns.val[second.val]! with
      | false => rfl
      | true => exact False.elim (hSecond ((mem_chosen cost selectedColumns second).mpr hFlag))
    obtain ⟨weight,hWeight⟩ := Option.ne_none_iff_exists'.mp hEdge
    rw [matrix_at_some cost first second weight hWeight]
    exact h.2 ((first.val,second.val),weight.val-rows.val[first.val]!.val-columns.val[second.val]!.val)
      ⟨first.val,first.isLt,second.val,second.isLt,hFirstFlag,hSecondFlag,weight,hWeight,rfl⟩
  exact ⟨row,column,hrow,hcolumn,hRow,hColumn,hAllowed,hDelta,hNonnegative,
    Assignment.adjust_feasible_on hf hNonnegative hCut,
    Assignment.adjust_creates_tight_edge (matrix cost) (potentialAt cost rows) (potentialAt cost columns)
      (chosen cost selectedRows) (chosen cost selectedColumns) cut.delta.val row column hRow hColumn hDelta⟩

/-- The actual Rust minimum-cut call returns an allowed, nonnegative attained
adjustment preserving the independent sparse dual and creating a tight edge.
Neither a minimum edge nor a source arithmetic/path certificate is supplied. -/
theorem minimum_sparse_cut_adjustment_spec (cost : Slice (alloc.vec.Vec (Option I64))) (rows columns : Slice I128)
    (selectedRows selectedColumns : Slice Bool) (h : Input cost rows columns selectedRows selectedColumns)
    (hf : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost rows) (potentialAt cost columns))
    (hcard : (chosen cost selectedRows).card = (chosen cost selectedColumns).card+1)
    (he : ∃ assignment : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) assignment) :
    sparse.minimum_sparse_cut cost rows columns selectedRows selectedColumns ⦃ result => ∃ cut,
      result = core.result.Result.Ok (some cut) ∧ Adjustment cost rows columns selectedRows selectedColumns cut ⦄ := by
  apply WP.spec_mono (minimum_sparse_cut_edges_spec cost rows columns selectedRows selectedColumns h)
  rintro result ⟨output,hResult,hMinimum⟩
  cases output with
  | none => exact False.elim (hMinimum (originalEntry_exists cost rows columns selectedRows selectedColumns hcard he))
  | some cut => exact ⟨cut,hResult,minimumCut_adjustment cost rows columns selectedRows selectedColumns cut hMinimum hf⟩

end SubtreeProofs.Rust.SparseCut

end
