module

public import SubtreeProofs.Rust.AssignmentSearchArithmetic
public import SubtreeProofs.Rust.AssignmentSearchCapacity
import Mathlib.Tactic

/-!
# Initial numeric and cut invariants from actual initialized vectors

Initial row potentials are the independent minima of the represented input
rows. Zero column potentials establish exact cumulative accounting and the
component envelope. Absent slacks and unused flags establish the empty cut.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentSearchInitialization

open AssignmentPotentialInitialization AssignmentNumericBounds AssignmentSearchArithmetic AssignmentScanCut

/-- Independent integer initial rows; the default applies only to empty
input rows, which cannot occur at a real row of a square matrix. -/
def initialRows (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (row : Fin n.val) : ℤ :=
  (minimumAt cost row.val).untopD 0

theorem initialized_rows (cost : Slice (alloc.vec.Vec I64)) (u : alloc.vec.Vec I128) (n : Usize)
    (hlen : cost.length = n.val) (hinit : Initialized cost u cost.length) :
    AssignmentAdjustmentFeasibility.potential n u = initialRows cost n := by
  funext row
  have hr : row.val < cost.length := by rw [hlen]; exact row.isLt
  have hm := hinit.2.2 row.val hr
  unfold initialRows
  rw [← hm,WithTop.untopD_coe]
  rfl

/-- The actual initialized minimum is an original signed i64 cost, so its
integer magnitude bound includes both extreme input values. -/
theorem initialized_row_bounds (cost : Slice (alloc.vec.Vec I64)) (u : alloc.vec.Vec I128) (n : Usize)
    (hlen : cost.length = n.val) (hinit : Initialized cost u cost.length) :
    ∀ row, -costMagnitude ≤ initialRows cost n row ∧ initialRows cost n row ≤ costMagnitude := by
  intro row
  have hr : row.val < cost.length := by rw [hlen]; exact row.isLt
  have hm := hinit.2.2 row.val hr
  have hmem := (List.minimum_eq_coe_iff.mp hm.symm).1
  obtain ⟨entry,_,he⟩ := List.mem_map.mp hmem
  have hrows := congrFun (initialized_rows cost u n hlen hinit) row
  change u.val[row.val+1]!.val = initialRows cost n row at hrows
  rw [← hrows,← he]
  unfold costMagnitude
  scalar_tac

/-- The actual initialized row minima and constant-zero column vector
establish all independent potential/search numeric invariants. -/
theorem initial_potentialInvariant (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128) (n : Usize)
    (hlen : cost.length = n.val) (hsquare : ∀ row ∈ cost.val, row.length = cost.length)
    (hinit : Initialized cost u cost.length) (hzero : v.val = List.replicate (n.val+1) 0#i128) :
    PotentialInvariant cost n (initialRows cost n) u v := by
  have hrows := initialized_rows cost u n hlen hinit
  have hcolumns : AssignmentAdjustmentFeasibility.potential n v = fun _ => 0 := by
    funext col
    simp [AssignmentAdjustmentFeasibility.potential,hzero]
  have hreserved : v.val[0]!.val = 0 := by simp [hzero]
  refine ⟨?_,?_,?_⟩
  · rw [hrows,hcolumns,hreserved,neg_zero]
    exact Assignment.envelope_initial _
  · rw [hrows,hcolumns,hreserved]
    simp
  · intro row col
    have hr : row.val < cost.length := by rw [hlen]; exact row.isLt
    have hc : col.val < cost.length := by rw [hlen]; exact col.isLt
    have h := initialized_feasible cost u hsquare hinit (⟨row.val,hr⟩ : Fin cost.length) (⟨col.val,hc⟩ : Fin cost.length)
    have hv := congrFun hcolumns col
    change u.val[row.val+1]!.val + AssignmentAdjustmentFeasibility.potential n v col ≤ _
    rw [hv]
    change u.val[row.val+1]!.val + 0 ≤ (cost.val[row.val]!).val[col.val]!.val
    simpa only [rowPotential,matrix] using h

/-- The actual absent-slack initializer establishes the independent empty
candidate minimum invariant for any predecessor-vector contents. -/
theorem initial_slackInvariant (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize)
    (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize) (n : Usize)
    (hslack : slack.val = List.replicate (n.val+1) none) :
    SlackInvariant cost u v matched used ∅ slack predecessor n := by
  intro target hp hb _
  have hi : target < n.val+1 := by omega
  have hnone : slack.val[target]! = none := by
    rw [hslack,getElem!_pos (List.replicate (n.val+1) (none : Option I128)) target (by simpa using hi)]
    simp
  rw [hnone]
  exact Assignment.minimumAt_empty _ _

/-- The actual unused-column initializer gives an empty candidate set. -/
theorem initial_usedIndices (used : alloc.vec.Vec Bool) (n : Usize)
    (hused : used.val = List.replicate (n.val+1) false) :
    AssignmentAdjustmentInvariant.usedIndices (alloc.vec.Vec.deref used) (n.val+1) = ∅ := by
  ext col
  simp [AssignmentAdjustmentInvariant.mem_usedIndices,alloc.vec.Vec.deref,Slice.from_val,hused]

end SubtreeProofs.Rust.AssignmentSearchInitialization

end
