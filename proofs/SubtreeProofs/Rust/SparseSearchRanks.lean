module

public import SubtreeProofs.Rust.SparseSearchGrowth
import Mathlib.Tactic

/-! # Exact discovery-rank writes for the actual sparse search -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentScanInvariant

theorem record_value (cost : Slice (alloc.vec.Vec (Option I64))) (values : alloc.vec.Vec Usize)
    (column value : Usize) (hl : values.length = cost.length) (hc : column.val < cost.length) (target : Vertex cost) :
    (values.set column value).val[target.val]!.val =
      if target.val = column.val then value.val else values.val[target.val]!.val := by
  by_cases he : target.val = column.val
  · rw [ite_eq_left he,he,vec_set_self values column value (by rw [hl]; exact hc)]
  · rw [ite_eq_right he,vec_set_other values column value target.val (by rw [hl]; exact target.isLt) (Ne.symm he)]

/-- The actual rank write marks exactly the newly discovered column with the
next positive visit count, leaving every other coordinate unchanged. -/
theorem record_discovery (cost : Slice (alloc.vec.Vec (Option I64))) (values : alloc.vec.Vec Usize)
    (oldColumns : Finset (Vertex cost)) (steps : Nat) (column next : Usize)
    (hl : values.length = cost.length) (hc : column.val < cost.length) (hn : next.val = steps+1)
    (he : ∀ target : Vertex cost, 0 < values.val[target.val]!.val ↔ target ∈ oldColumns)
    (hb : ∀ target : Vertex cost, values.val[target.val]!.val ≤ steps) :
    (∀ target : Vertex cost, 0 < (values.set column next).val[target.val]!.val ↔ target ∈ insert ⟨column.val,hc⟩ oldColumns) ∧
    (∀ target : Vertex cost, (values.set column next).val[target.val]!.val ≤ next.val) := by
  constructor
  · intro target
    rw [record_value cost values column next hl hc target,Finset.mem_insert]
    by_cases hh : target.val = column.val
    · have ht : target = (⟨column.val,hc⟩ : Vertex cost) := Fin.ext hh
      rw [ite_eq_left hh]
      exact iff_of_true (by omega) (Or.inl ht)
    · have ht : target ≠ (⟨column.val,hc⟩ : Vertex cost) := fun h => hh (congrArg Fin.val h)
      simpa only [hh,ht,↓reduceIte,false_or] using he target
  · intro target
    rw [record_value cost values column next hl hc target]
    split
    · exact le_refl _
    · have hh := hb target
      omega

/-- A newly discovered predecessor points either directly to the free root,
or to a strictly earlier discovered matched column, in the actual rank array
after its write. This is the local acyclicity needed for path reconstruction. -/
theorem new_predecessor_rank (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) (step : sparse.SparseStep) (next : Usize) (hn : next.val = steps.val+1)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    ∃ row column : Vertex cost, row.val = step.cut.row.val ∧ column.val = step.cut.column.val ∧
      (row = root ∨ 0 < (discovery.set step.cut.column next).val[(assignment row).val]!.val ∧
        (discovery.set step.cut.column next).val[(assignment row).val]!.val <
          (discovery.set step.cut.column next).val[column.val]!.val) := by
  obtain ⟨row,column,hRow,hColumn,hSelected,hUnselected,hAllowed,hDelta,hTight⟩ := hp.tight_edge
  have hc : step.cut.column.val < cost.length := by rw [← hColumn]; exact column.isLt
  refine ⟨row,column,hRow,hColumn,?_⟩
  have hr : row = root ∨ assignment row ∈ chosen cost (alloc.vec.Vec.deref selectedColumns) := by
    rw [h.rows_exact,Assignment.mem_searchRows] at hSelected
    exact hSelected
  rcases hr with he | he
  · exact Or.inl he
  · right
    have hncol : (assignment row).val ≠ step.cut.column.val := by
      intro hh
      have hsame : assignment row = column := Fin.ext (hh.trans hColumn.symm)
      exact hUnselected (hsame ▸ he)
    have hpos : 0 < discovery.val[(assignment row).val]!.val := by
      apply (h.discovery_exact (assignment row)).mpr
      simpa only [discovered,hs,↓reduceIte,Finset.union_empty] using he
    rw [record_value cost discovery step.cut.column next h.discovery_length hc (assignment row),
      ite_eq_right hncol,record_value cost discovery step.cut.column next h.discovery_length hc column,ite_eq_left hColumn]
    exact ⟨hpos,by have hb := h.discovery_bound (assignment row); omega⟩

/-- Recording a fresh column preserves all previous predecessor edges and
their decreasing ranks in the actual updated arrays and potentials. -/
theorem recorded_old_predecessors (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) (step : sparse.SparseStep) (next : Usize)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    ∀ column ∈ chosen cost (alloc.vec.Vec.deref selectedColumns), ∃ row : Vertex cost,
      (predecessor.set step.cut.column step.cut.row).val[column.val]!.val = row.val ∧
      row ∈ chosen cost (alloc.vec.Vec.deref selectedRows) ∧ allowed cost row column ∧
      potentialAt cost (alloc.vec.Vec.deref step.rows) row+potentialAt cost (alloc.vec.Vec.deref step.columns) column = matrix cost row column ∧
      (row = root ∨ 0 < (discovery.set step.cut.column next).val[(assignment row).val]!.val ∧
        (discovery.set step.cut.column next).val[(assignment row).val]!.val <
          (discovery.set step.cut.column next).val[column.val]!.val) := by
  obtain ⟨newRow,newColumn,hNewRow,hNewColumn,hSelected,hUnselected,hAllowed,hDelta,hTight⟩ := hp.tight_edge
  have hc : step.cut.column.val < cost.length := by rw [← hNewColumn]; exact newColumn.isLt
  have hne : ∀ column ∈ chosen cost (alloc.vec.Vec.deref selectedColumns), column.val ≠ step.cut.column.val := by
    intro column hColumn he
    have hh : column = newColumn := Fin.ext (he.trans hNewColumn.symm)
    exact hUnselected (hh ▸ hColumn)
  intro column hColumn
  obtain ⟨row,hPred,hRow,hEdge,hTight',hRank⟩ :=
    step_old_predecessors cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns
      predecessor discovery steps searching failure h hs step hp column hColumn
  refine ⟨row,?_,hRow,hEdge,hTight',?_⟩
  · rw [record_value cost predecessor step.cut.column step.cut.row h.predecessor_length hc column,ite_eq_right (hne column hColumn)]
    exact hPred
  · rcases hRank with he | ⟨hPositive,hLess⟩
    · exact Or.inl he
    · right
      have hParent : assignment row ∈ chosen cost (alloc.vec.Vec.deref selectedColumns) := by
        have hh := (h.discovery_exact (assignment row)).mp hPositive
        simpa only [discovered,hs,↓reduceIte,Finset.union_empty] using hh
      rw [record_value cost discovery step.cut.column next h.discovery_length hc column,ite_eq_right (hne column hColumn),
        record_value cost discovery step.cut.column next h.discovery_length hc (assignment row),ite_eq_right (hne (assignment row) hParent)]
      exact ⟨hPositive,hLess⟩

end SubtreeProofs.Rust.SparseSearch

end
