module

public import SubtreeProofs.Rust.SparseSearchPreservation
import Mathlib.Tactic

/-! # Finite total correctness of the actual sparse alternating-search loop -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentNumericBounds

def Stopped (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (output : SearchOutput) : Prop :=
  let (rows,columns,predecessor,discovery,steps,failure) := output
  ∃ selectedRows selectedColumns increment,
    Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps false failure

/-- The actual sparse loop terminates without a failure and retains the full
independent invariant with the free target discovered. Its finite measure is
the remaining visit budget, including the final stopped-state iteration. -/
theorem find_sparse_augmenting_path_loop_spec (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure) :
    sparse_search.find_sparse_augmenting_path_loop cost rows columns n inverse target selectedRows selectedColumns predecessor discovery steps searching failure ⦃ output =>
      Stopped cost assignment root initialRows initialColumns output ⦄ := by
  unfold sparse_search.find_sparse_augmenting_path_loop
  apply loop.spec_decr_nat (fun state : SearchState => n.val+1-state.2.2.2.2.2.2.1.val)
    (StateInvariant cost assignment root initialRows initialColumns)
    (Stopped cost assignment root initialRows initialColumns) _ _ ?_ ⟨increment,h⟩
  rintro ⟨currentRows,currentColumns,rowFlags,columnFlags,parents,ranks,visits,active,error⟩ ⟨inc,hCurrent⟩
  cases active with
  | false =>
    unfold sparse_search.find_sparse_augmenting_path_loop.body
    simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok]
    exact ⟨rowFlags,columnFlags,inc,hCurrent⟩
  | true =>
    apply WP.spec_mono (body_preserves_spec cost n assignment root inverse target initialRows initialColumns inc
      currentRows currentColumns rowFlags columnFlags parents ranks visits true error input hCurrent rfl)
    intro result hResult
    cases result with
    | done output => exact False.elim hResult
    | cont state => exact hResult

/-- Independent original-coordinate path certificate exported by the source
search. Every recorded predecessor edge is real and tight, and every link to
a nonroot predecessor decreases a positive rank bounded by the visit count. -/
structure PathCertificate (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (result : sparse_search.SparseSearch) : Prop where
  rows_length : result.rows.length = cost.length
  columns_length : result.columns.length = cost.length
  predecessor_length : result.predecessor_row.length = cost.length
  discovery_length : result.discovery.length = cost.length
  target_eq : result.target.val = (assignment root).val
  steps_bound : result.steps.val ≤ cost.length
  feasible : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref result.rows)) (potentialAt cost (alloc.vec.Vec.deref result.columns))
  matching_tight : ∀ row, row ≠ root → potentialAt cost (alloc.vec.Vec.deref result.rows) row+
    potentialAt cost (alloc.vec.Vec.deref result.columns) (assignment row) = matrix cost row (assignment row)
  numeric : ∃ increment, Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref result.rows))
      (potentialAt cost (alloc.vec.Vec.deref result.columns)) increment ∧
    Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref result.rows)) (potentialAt cost (alloc.vec.Vec.deref result.columns)) =
      Assignment.dualValue initialRows initialColumns+increment ∧ increment ≤ cumulativeBound cost.length
  target_discovered : 0 < result.discovery.val[(assignment root).val]!.val
  discovery_bound : ∀ column : Vertex cost, result.discovery.val[column.val]!.val ≤ result.steps.val
  predecessor_edges : ∀ column : Vertex cost, 0 < result.discovery.val[column.val]!.val → ∃ row : Vertex cost,
    result.predecessor_row.val[column.val]!.val = row.val ∧ allowed cost row column ∧
    potentialAt cost (alloc.vec.Vec.deref result.rows) row+potentialAt cost (alloc.vec.Vec.deref result.columns) column = matrix cost row column ∧
    (row = root ∨ 0 < result.discovery.val[(assignment row).val]!.val ∧
      result.discovery.val[(assignment row).val]!.val < result.discovery.val[column.val]!.val)

theorem Stopped.certificate (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ)
    (input : Input cost n assignment root inverse target initialRows initialColumns) (output : SearchOutput)
    (h : Stopped cost assignment root initialRows initialColumns output) :
    output.2.2.2.2.2 = none ∧
      PathCertificate cost assignment root initialRows initialColumns
        ⟨output.1,output.2.1,output.2.2.1,output.2.2.2.1,target,output.2.2.2.2.1⟩ := by
  rcases output with ⟨rows,columns,predecessor,discovery,steps,failure⟩
  obtain ⟨selectedRows,selectedColumns,increment,hi⟩ := h
  dsimp only
  refine ⟨hi.failure_none,{
    rows_length := hi.rows_length
    columns_length := hi.columns_length
    predecessor_length := hi.predecessor_length
    discovery_length := hi.discovery_length
    target_eq := input.target_eq
    steps_bound := ?_
    feasible := hi.feasible
    matching_tight := hi.matching_tight
    numeric := ?_
    target_discovered := ?_
    discovery_bound := hi.discovery_bound
    predecessor_edges := ?_
  }⟩
  · change steps.val ≤ cost.length
    have hb := Assignment.search_cut_card_lt assignment root (chosen cost (alloc.vec.Vec.deref selectedColumns)) hi.free_outside
    have hs := hi.steps_card
    simp only [Bool.false_eq_true,↓reduceIte] at hs
    simp only [Vertex,Fintype.card_fin] at hb
    omega
  · refine ⟨increment,hi.envelope,hi.account,?_⟩
    have hb := Assignment.total_increment_bound_both_on initialRows initialColumns _ _ costMagnitude 0 increment
      (fun row => (input.initial_rows row).1) (fun column => (input.initial_columns column).1)
      input.cost_upper hi.feasible input.compatible hi.account
    simp only [Vertex,Fintype.card_fin,zero_add] at hb
    unfold cumulativeBound
    nlinarith
  · apply (hi.discovery_exact (assignment root)).mpr
    simp [discovered]
  · intro column hPositive
    obtain ⟨row,hPred,hSelected,hAllowed,hTight,hRank⟩ := hi.predecessor_edges column ((hi.discovery_exact column).mp hPositive)
    exact ⟨row,hPred,hAllowed,hTight,hRank⟩

end SubtreeProofs.Rust.SparseSearch

end
