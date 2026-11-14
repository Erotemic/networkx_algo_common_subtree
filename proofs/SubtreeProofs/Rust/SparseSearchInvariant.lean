module

public import SubtreeProofs.Rust.SparseSearchFlags
import Mathlib.Tactic

/-! # Independent invariant for the actual zero-based sparse alternating search -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentNumericBounds

structure Input (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) : Prop where
  n_eq : n.val = cost.length
  size : cost.length ≤ U32.max
  square : Square cost
  inverse_length : inverse.length = cost.length
  inverse_values : ∀ column : Vertex cost, inverse.val[column.val]!.val = (assignment.symm column).val
  target_eq : target.val = (assignment root).val
  initial_rows : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0
  initial_columns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0
  cost_upper : ∀ row column, allowed cost row column → matrix cost row column ≤ 0
  compatible : ∃ replacement : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) replacement

/-- Columns with recorded predecessors include the free target exactly when
the search has stopped. The source leaves its selected-column flag false. -/
def discovered (cost : Slice (alloc.vec.Vec (Option I64))) (columns : alloc.vec.Vec Bool)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (searching : Bool) : Finset (Vertex cost) :=
  chosen cost (alloc.vec.Vec.deref columns) ∪ if searching then ∅ else {assignment root}

structure Invariant (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError) : Prop where
  rows_length : rows.length = cost.length
  columns_length : columns.length = cost.length
  selected_rows_length : selectedRows.length = cost.length
  selected_columns_length : selectedColumns.length = cost.length
  predecessor_length : predecessor.length = cost.length
  discovery_length : discovery.length = cost.length
  failure_none : failure = none
  rows_exact : chosen cost (alloc.vec.Vec.deref selectedRows) = Assignment.searchRows assignment root (chosen cost (alloc.vec.Vec.deref selectedColumns))
  free_outside : assignment root ∉ chosen cost (alloc.vec.Vec.deref selectedColumns)
  steps_card : steps.val = (chosen cost (alloc.vec.Vec.deref selectedColumns)).card + if searching then 0 else 1
  feasible : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns))
  matching_tight : ∀ row, row ≠ root →
    potentialAt cost (alloc.vec.Vec.deref rows) row+potentialAt cost (alloc.vec.Vec.deref columns) (assignment row) = matrix cost row (assignment row)
  envelope : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) increment
  account : Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) =
    Assignment.dualValue initialRows initialColumns+increment
  discovery_exact : ∀ column : Vertex cost, 0 < discovery.val[column.val]!.val ↔ column ∈ discovered cost selectedColumns assignment root searching
  discovery_bound : ∀ column : Vertex cost, discovery.val[column.val]!.val ≤ steps.val
  predecessor_edges : ∀ column ∈ discovered cost selectedColumns assignment root searching, ∃ row : Vertex cost,
    predecessor.val[column.val]!.val = row.val ∧ row ∈ chosen cost (alloc.vec.Vec.deref selectedRows) ∧ allowed cost row column ∧
    potentialAt cost (alloc.vec.Vec.deref rows) row+potentialAt cost (alloc.vec.Vec.deref columns) column = matrix cost row column ∧
    (row = root ∨ 0 < discovery.val[(assignment row).val]!.val ∧
      discovery.val[(assignment row).val]!.val < discovery.val[column.val]!.val)

abbrev SearchState := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Bool × alloc.vec.Vec Bool ×
  alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize × Bool × Option AssignmentError

abbrev SearchOutput := alloc.vec.Vec I128 × alloc.vec.Vec I128 × alloc.vec.Vec Usize × alloc.vec.Vec Usize × Usize × Option AssignmentError

def StateInvariant (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (state : SearchState) : Prop :=
  let (rows,columns,selectedRows,selectedColumns,predecessor,discovery,steps,searching,failure) := state
  ∃ increment, Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure

theorem Invariant.cut_card (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure) :
    (chosen cost (alloc.vec.Vec.deref selectedRows)).card = (chosen cost (alloc.vec.Vec.deref selectedColumns)).card+1 := by
  rw [h.rows_exact]
  exact Assignment.searchRows_card assignment root _ h.free_outside

theorem Invariant.visit_guard (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (hn : n.val = cost.length)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) : steps.val < n.val := by
  have hc := Assignment.search_cut_card_lt assignment root (chosen cost (alloc.vec.Vec.deref selectedColumns)) h.free_outside
  have hsteps := h.steps_card
  simp only [hs,↓reduceIte,Nat.add_zero] at hsteps
  simpa only [Vertex,Fintype.card_fin,← hn,← hsteps] using hc

/-- The whole source invariant discharges the complete selector/update
primitive's input, cardinality, existence and arithmetic obligations. -/
theorem Invariant.advance_spec (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure) :
    sparse.advance_sparse_cut cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) ⦃ result => ∃ step,
        result = core.result.Result.Ok (some step) ∧ StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
          (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step ⦄ := by
  exact advance_sparse_cut_spec cost _ _ _ _
    (by simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using h.rows_length)
    (by simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using h.columns_length)
    (by simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using h.selected_rows_length)
    (by simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using h.selected_columns_length)
    input.square input.size initialRows initialColumns increment input.initial_rows input.initial_columns
    h.envelope h.account h.feasible input.cost_upper input.compatible (h.cut_card cost assignment root initialRows initialColumns increment _ _ _ _ _ _ _ _ _)

end SubtreeProofs.Rust.SparseSearch

end
