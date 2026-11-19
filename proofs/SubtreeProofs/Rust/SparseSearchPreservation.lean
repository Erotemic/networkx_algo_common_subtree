module

public import SubtreeProofs.Rust.SparseSearchRanks
import Mathlib.Tactic

/-! # Complete invariant preservation by an actual sparse search iteration -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut

theorem afterStep_invariant (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) (step : sparse.SparseStep) (next : Usize) (hn : next.val = steps.val+1)
    (hp : StepProgress cost (alloc.vec.Vec.deref rows) (alloc.vec.Vec.deref columns)
      (alloc.vec.Vec.deref selectedRows) (alloc.vec.Vec.deref selectedColumns) initialRows initialColumns increment step) :
    let (newRows,newColumns,newSelectedRows,newSelectedColumns,newPredecessor,newDiscovery,newSteps,newSearching,newFailure) :=
      afterStep inverse target selectedRows selectedColumns predecessor discovery step next
    Invariant cost assignment root initialRows initialColumns (increment+step.cut.delta.val)
      newRows newColumns newSelectedRows newSelectedColumns newPredecessor newDiscovery newSteps newSearching newFailure := by
  obtain ⟨hc,hFrame⟩ := step_cut_frame cost n assignment root inverse target initialRows initialColumns increment rows columns
    selectedRows selectedColumns predecessor discovery steps searching failure input h hs step next hn hp
  have hOldRank : ∀ column : Vertex cost, 0 < discovery.val[column.val]!.val ↔ column ∈ chosen cost (alloc.vec.Vec.deref selectedColumns) := by
    intro column
    simpa only [discovered,hs,↓reduceIte,Finset.union_empty] using h.discovery_exact column
  have hRecorded := record_discovery cost discovery (chosen cost (alloc.vec.Vec.deref selectedColumns)) steps.val step.cut.column next
    h.discovery_length hc hn hOldRank h.discovery_bound
  dsimp only [afterStep]
  refine {
    rows_length := hp.rows_length
    columns_length := hp.columns_length
    selected_rows_length := hFrame.rows_length
    selected_columns_length := hFrame.columns_length
    predecessor_length := by simpa using h.predecessor_length
    discovery_length := by simpa using h.discovery_length
    failure_none := rfl
    rows_exact := hFrame.rows_exact
    free_outside := hFrame.free_outside
    steps_card := hFrame.steps_card
    feasible := hp.feasible
    matching_tight := step_matching_tight cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns
      predecessor discovery steps searching failure h step hp
    envelope := hp.envelope
    account := hp.account
    discovery_exact := ?_
    discovery_bound := hRecorded.2
    predecessor_edges := ?_
  }
  · intro column
    rw [hFrame.discovered_exact]
    exact hRecorded.1 column
  · intro column hColumn
    rw [hFrame.discovered_exact] at hColumn
    rcases Finset.mem_insert.mp hColumn with he | he
    · subst column
      obtain ⟨row,column,hRow,hCol,hSelected,hUnselected,hAllowed,hDelta,hTight⟩ := hp.tight_edge
      have hColumnEq : column = (⟨step.cut.column.val,hc⟩ : Vertex cost) := Fin.ext hCol
      subst column
      refine ⟨row,?_,hFrame.rows_mono hSelected,hAllowed,hTight,?_⟩
      · rw [record_value cost predecessor step.cut.column step.cut.row h.predecessor_length hc,ite_eq_left rfl]
        exact hRow.symm
      · obtain ⟨rankRow,rankColumn,hRankRow,hRankColumn,hRank⟩ := new_predecessor_rank cost assignment root initialRows initialColumns increment
          rows columns selectedRows selectedColumns predecessor discovery steps searching failure h hs step next hn hp
        have hr : rankRow = row := Fin.ext (hRankRow.trans hRow.symm)
        have hcol : rankColumn = (⟨step.cut.column.val,hc⟩ : Vertex cost) := Fin.ext hRankColumn
        simpa only [hr,hcol] using hRank
    · obtain ⟨row,hPred,hSelected,hAllowed,hTight,hRank⟩ := recorded_old_predecessors cost assignment root initialRows initialColumns increment
        rows columns selectedRows selectedColumns predecessor discovery steps searching failure h hs step next hp column he
      exact ⟨row,hPred,hFrame.rows_mono hSelected,hAllowed,hTight,hRank⟩

/-- Actual active Rust iterations preserve the complete independent invariant
and strictly decrease the source loop's finite visit measure. -/
theorem body_preserves_spec (cost : Slice (alloc.vec.Vec (Option I64))) (n : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (inverse : alloc.vec.Vec Usize) (target : Usize)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (rows columns : alloc.vec.Vec I128) (selectedRows selectedColumns : alloc.vec.Vec Bool)
    (predecessor discovery : alloc.vec.Vec Usize) (steps : Usize) (searching : Bool) (failure : Option AssignmentError)
    (input : Input cost n assignment root inverse target initialRows initialColumns)
    (h : Invariant cost assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns predecessor discovery steps searching failure)
    (hs : searching = true) :
    sparse_search.find_sparse_augmenting_path_loop.body cost n inverse target rows columns selectedRows selectedColumns predecessor discovery steps searching failure ⦃ result =>
      match result with
      | .done _ => False
      | .cont state => StateInvariant cost assignment root initialRows initialColumns state ∧
          n.val+1-state.2.2.2.2.2.2.1.val < n.val+1-steps.val ⦄ := by
  apply WP.spec_mono (body_step_spec cost n assignment root inverse target initialRows initialColumns increment rows columns selectedRows selectedColumns
    predecessor discovery steps searching failure input h hs)
  rintro result ⟨step,next,hProgress,hNext,rfl⟩
  constructor
  · exact ⟨increment+step.cut.delta.val,afterStep_invariant cost n assignment root inverse target initialRows initialColumns increment rows columns
      selectedRows selectedColumns predecessor discovery steps searching failure input h hs step next hNext hProgress⟩
  · have hv := h.visit_guard cost n assignment root initialRows initialColumns increment rows columns selectedRows selectedColumns
      predecessor discovery steps searching failure input.n_eq hs
    dsimp only [afterStep]
    omega

end SubtreeProofs.Rust.SparseSearch

end
