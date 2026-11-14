module

public import SubtreeProofs.Shared.AssignmentFiniteDeletion
public import SubtreeProofs.Shared.AssignmentReindex
import Mathlib.Tactic

/-! # Compact deletion warm starts retain feasibility and numeric accounting -/

@[expose] public section

namespace SubtreeProofs.AssignmentVertexDeletion

variable {n : Nat} {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Restricting a zero-baseline identity vertex and compacting the surviving
original coordinates preserves the full two-sided numeric state. The new
increment obeys the surviving dimension's budget, before executing repair. -/
theorem compact_deletion_state (edges : Fin (n+1) → Fin (n+1) → Prop) (matrix : Fin (n+1) → Fin (n+1) → K)
    (initialRows initialColumns rows columns : Fin (n+1) → K) (increment bound : K) (removed : Fin (n+1))
    (hIdentity : ∀ vertex, edges vertex vertex) (hZero : matrix removed removed = 0)
    (hInitialRow : initialRows removed = 0) (hInitialColumn : initialColumns removed = 0)
    (hRowLower : ∀ row, -bound ≤ initialRows row) (hColumnLower : ∀ column, -bound ≤ initialColumns column)
    (hUpper : ∀ row column, edges row column → matrix row column ≤ 0)
    (hFeasible : Assignment.FeasibleOn edges matrix rows columns)
    (hEnvelope : Assignment.BiEnvelope initialRows initialColumns rows columns increment)
    (hAccount : Assignment.dualValue rows columns = Assignment.dualValue initialRows initialColumns+increment) :
    let expand := removed.succAbove
    let next := increment-(rows removed+columns removed)
    Assignment.FeasibleOn (fun row column => edges (expand row) (expand column)) (fun row column => matrix (expand row) (expand column))
      (fun row => rows (expand row)) (fun column => columns (expand column)) ∧
    Assignment.BiEnvelope (fun row => initialRows (expand row)) (fun column => initialColumns (expand column))
      (fun row => rows (expand row)) (fun column => columns (expand column)) next ∧
    Assignment.dualValue (fun row => rows (expand row)) (fun column => columns (expand column)) =
      Assignment.dualValue (fun row => initialRows (expand row)) (fun column => initialColumns (expand column))+next ∧
    next ≤ 2*(n : K)*bound := by
  dsimp only
  have hi : rows removed+columns removed ≤ 0 := by simpa only [hZero] using hFeasible removed removed (hIdentity removed)
  have hd := hEnvelope.delete removed hInitialRow hInitialColumn hi hAccount
  have hNewEnvelope : Assignment.BiEnvelope (fun row => initialRows (removed.succAbove row)) (fun column => initialColumns (removed.succAbove column))
      (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column))
      (increment-(rows removed+columns removed)) := hd.1.reindex (remainingEquiv removed)
  have hNewAccount : Assignment.dualValue (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column)) =
      Assignment.dualValue (fun row => initialRows (removed.succAbove row)) (fun column => initialColumns (removed.succAbove column))+
        (increment-(rows removed+columns removed)) := by
    change Assignment.dualValue (fun row => rows (remainingEquiv removed row).val) (fun column => columns (remainingEquiv removed column).val) =
      Assignment.dualValue (fun row => initialRows (remainingEquiv removed row).val) (fun column => initialColumns (remainingEquiv removed column).val)+_
    rw [Assignment.dualValue_reindex (remainingEquiv removed) (fun row => rows row.val) (fun column => columns column.val),
      Assignment.dualValue_reindex (remainingEquiv removed) (fun row => initialRows row.val) (fun column => initialColumns column.val)]
    exact hd.2
  have hNewFeasible : Assignment.FeasibleOn (fun row column => edges (removed.succAbove row) (removed.succAbove column))
      (fun row column => matrix (removed.succAbove row) (removed.succAbove column))
      (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column)) :=
    fun row column he => hFeasible (removed.succAbove row) (removed.succAbove column) he
  refine ⟨hNewFeasible,hNewEnvelope,hNewAccount,?_⟩
  have he : ∃ assignment : Equiv.Perm (Fin n), Assignment.Compatible (fun row column => edges (removed.succAbove row) (removed.succAbove column)) assignment :=
    ⟨1,fun row => hIdentity (removed.succAbove row)⟩
  have hb := Assignment.total_increment_bound_both_on (fun row => initialRows (removed.succAbove row)) (fun column => initialColumns (removed.succAbove column))
    (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column)) bound 0 (increment-(rows removed+columns removed))
    (fun row => hRowLower _) (fun column => hColumnLower _) (fun row column he => hUpper _ _ he) hNewFeasible he hNewAccount
  simp only [Fintype.card_fin,zero_add] at hb
  nlinarith

/-- The actual compact temporary completion retains every old allowed tight
edge except at its unique free root. This is the one-deficit augmentation seed. -/
theorem compact_seed (edges : Fin (n+1) → Fin (n+1) → Prop) (matrix : Fin (n+1) → Fin (n+1) → K)
    (rows columns : Fin (n+1) → K) (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed ≠ removed) (hAllowed : Assignment.Compatible edges assignment)
    (hTight : Assignment.Tight matrix rows columns assignment) :
    ∀ row, row ≠ compactFree assignment removed hn →
      edges (removed.succAbove row) (removed.succAbove (compactAssignment assignment removed row)) ∧
      rows (removed.succAbove row)+columns (removed.succAbove (compactAssignment assignment removed row)) =
        matrix (removed.succAbove row) (removed.succAbove (compactAssignment assignment removed row)) := by
  intro row hr
  rw [compactAssignment_away assignment removed hn row hr]
  exact ⟨hAllowed _,hTight _⟩

/-- Deleting a fixed assignment vertex needs no repair. The canonical compact
permutation retains every old allowed tight edge and is independently minimum
under the surviving feasible dual. No identity-edge hypothesis is needed. -/
theorem compact_paired_optimum (edges : Fin (n+1) → Fin (n+1) → Prop)
    (matrix : Fin (n+1) → Fin (n+1) → K) (rows columns : Fin (n+1) → K)
    (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hPaired : assignment removed = removed)
    (hFeasible : Assignment.FeasibleOn edges matrix rows columns)
    (hAllowed : Assignment.Compatible edges assignment)
    (hTight : Assignment.Tight matrix rows columns assignment) :
    Assignment.IsMinimumOn (fun row column => edges (removed.succAbove row) (removed.succAbove column))
      (fun row column => matrix (removed.succAbove row) (removed.succAbove column)) (compactAssignment assignment removed) ∧
    Assignment.Tight (fun row column => matrix (removed.succAbove row) (removed.succAbove column))
      (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column))
      (compactAssignment assignment removed) := by
  have ha : Assignment.Compatible (fun row column => edges (removed.succAbove row) (removed.succAbove column))
      (compactAssignment assignment removed) := by
    intro row
    rw [compactAssignment_paired assignment removed hPaired row]
    exact hAllowed _
  have ht : Assignment.Tight (fun row column => matrix (removed.succAbove row) (removed.succAbove column))
      (fun row => rows (removed.succAbove row)) (fun column => columns (removed.succAbove column))
      (compactAssignment assignment removed) := by
    intro row
    dsimp only
    rw [compactAssignment_paired assignment removed hPaired row]
    exact hTight _
  exact ⟨Assignment.isMinimumOn_of_feasible_tight
    (fun row column he => hFeasible (removed.succAbove row) (removed.succAbove column) he) ha ht,ht⟩

end SubtreeProofs.AssignmentVertexDeletion

end
