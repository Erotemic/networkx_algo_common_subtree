module

public import SubtreeProofs.Shared.AssignmentEnvelope
public import SubtreeProofs.Rust.AssignmentCutFeasibility
import Mathlib.Tactic

/-!
# Derived machine bounds for the actual Hungarian arithmetic

The i64 cost magnitude is 2^63, including its minimum value. An accepted
u32-sized dimension bounds cumulative ideal adjustments by twice dimension
times that magnitude. All potential and reduced-cost ranges then fit i128.
These lemmas derive the numeric premises of actual scan/adjustment proofs.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentNumericBounds

open AssignmentColumnScan AssignmentScanInvariant AssignmentAdjustmentFeasibility

def costMagnitude : ℤ := 2^63

def cumulativeBound (n : Nat) : ℤ := 2*(n : ℤ)*costMagnitude

def reducedBound (n : Nat) : ℤ := 2*costMagnitude+cumulativeBound n

/-- The conservative range for all search arithmetic fits the real signed
machine type at every dimension accepted by the public API. -/
theorem fits128_of_bound (n : Nat) (value : ℤ) (hn : n ≤ U32.max)
    (hlower : -reducedBound n ≤ value) (hupper : value ≤ reducedBound n) : Fits128 value := by
  unfold reducedBound cumulativeBound costMagnitude at hlower hupper
  constructor <;> scalar_tac

theorem reducedBound_nonnegative (n : Nat) : 0 ≤ reducedBound n := by
  unfold reducedBound cumulativeBound costMagnitude
  positivity

theorem cost_bounds (cost : Slice (alloc.vec.Vec I64)) (n : Usize) :
    ∀ row col, -costMagnitude ≤ AssignmentReconstruction.matrix cost n row col ∧
      AssignmentReconstruction.matrix cost n row col ≤ costMagnitude := by
  intro row col
  unfold AssignmentReconstruction.matrix costMagnitude
  scalar_tac

/-- Component envelopes yield representable actual real potentials without
assuming checked arithmetic has already succeeded. -/
theorem envelope_values_fit {A : Type*} (initialRows rows columns : A → ℤ) (increment : ℤ) (n : Nat)
    (hn : n ≤ U32.max) (henvelope : Assignment.Envelope initialRows rows columns increment)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (hincrement : increment ≤ cumulativeBound n) :
    (∀ row, Fits128 (rows row)) ∧ (∀ col, Fits128 (columns col)) := by
  have hm : 0 ≤ costMagnitude := by norm_num [costMagnitude]
  have hb : 0 ≤ cumulativeBound n := by unfold cumulativeBound; positivity
  constructor
  · intro row
    apply fits128_of_bound n _ hn
    · have hl := henvelope.row_lower row
      have hi := (hinitial row).1
      unfold reducedBound
      linarith
    · have hu := henvelope.row_upper row
      have hi := (hinitial row).2
      unfold reducedBound
      linarith
  · intro col
    apply fits128_of_bound n _ hn
    · have hl := henvelope.column_lower col
      unfold reducedBound
      linarith
    · exact (henvelope.column_upper col).trans (reducedBound_nonnegative n)

/-- Reserved column zero stores the negative cumulative adjustment, which
also fits i128 under the independently derived cumulative bound. -/
theorem reserved_value_fits (n : Nat) (increment : ℤ) (hn : n ≤ U32.max)
    (hpositive : 0 ≤ increment) (hbound : increment ≤ cumulativeBound n) : Fits128 (-increment) := by
  have hm : 0 ≤ costMagnitude := by norm_num [costMagnitude]
  apply fits128_of_bound n _ hn
  · unfold reducedBound
    linarith
  · exact (neg_nonpos.mpr hpositive).trans (reducedBound_nonnegative n)

/-- Minimum selection ensures finite unused slacks remain representable when
the actual adjustment is subtracted. -/
theorem slack_subtraction_fits (n : Nat) (slack amount : ℤ) (hn : n ≤ U32.max)
    (hslack : slack ≤ reducedBound n) (hamount : 0 ≤ amount) (hminimum : amount ≤ slack) : Fits128 (slack-amount) := by
  apply fits128_of_bound n _ hn
  · have hb := reducedBound_nonnegative n
    linarith
  · linarith

/-- The component/feasibility invariant supplies both checked-subtraction
premises for the actual source column scan. -/
theorem scan_subtractions_fit (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (n activeRow candidate : Usize) (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (hn : n.val ≤ U32.max) (hrp : 0 < activeRow.val) (hrb : activeRow.val ≤ n.val)
    (hcp : 0 < candidate.val) (hcb : candidate.val ≤ n.val)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (hincrement : increment ≤ cumulativeBound n.val)
    (hfeasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v)) :
    Fits128 (firstReduced cost (alloc.vec.Vec.deref u) activeRow candidate) ∧
      Fits128 (reducedCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) activeRow candidate) := by
  let row : Fin n.val := ⟨activeRow.val-1,by omega⟩
  let col : Fin n.val := ⟨candidate.val-1,by omega⟩
  have hri : row.val+1 = activeRow.val := by dsimp only [row]; omega
  have hci : col.val+1 = candidate.val := by dsimp only [col]; omega
  have hb := henvelope.reduced_bounds hfeasible (cost_bounds cost n) hinitial row col
  have hfirst : firstReduced cost (alloc.vec.Vec.deref u) activeRow candidate =
      AssignmentReconstruction.matrix cost n row col - potential n u row := by
    simp only [firstReduced,inputCost,alloc.vec.Vec.deref,Slice.from_val,AssignmentReconstruction.matrix,potential,hri]
    rfl
  have hreduced : reducedCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) activeRow candidate =
      AssignmentReconstruction.matrix cost n row col - potential n u row - potential n v col := by
    unfold reducedCost
    rw [hfirst]
    simp only [alloc.vec.Vec.deref,Slice.from_val,potential,hci]
  have hm : 0 ≤ costMagnitude := by norm_num [costMagnitude]
  have htotal := reducedBound_nonnegative n.val
  constructor
  · rw [hfirst]
    apply fits128_of_bound n.val _ hn
    · unfold reducedBound
      linarith [hb.1.1]
    · unfold reducedBound at htotal ⊢
      have hi := henvelope.nonnegative
      linarith [hb.1.2]
  · rw [hreduced]
    apply fits128_of_bound n.val _ hn
    · linarith [hb.2.1]
    · unfold reducedBound
      linarith [hb.2.2]


/-- Every real cut candidate cost has a uniform nonnegative bound, which
also bounds any finite slack attained by a stored predecessor. -/
theorem candidate_cost_range (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (n : Usize) (initialRows : Fin n.val → ℤ) (increment : ℤ)
    (henvelope : Assignment.Envelope initialRows (potential n u) (potential n v) increment)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (hincrement : increment ≤ cumulativeBound n.val)
    (hfeasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v))
    (target candidate : Nat) (htp : 0 < target) (htb : target ≤ n.val)
    (hrp : 0 < matched.val[candidate]!.val) (hrb : matched.val[candidate]!.val ≤ n.val) :
    0 ≤ AssignmentScanCut.candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate ∧
      AssignmentScanCut.candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate ≤ reducedBound n.val := by
  let row : Fin n.val := ⟨matched.val[candidate]!.val-1,by omega⟩
  let col : Fin n.val := ⟨target-1,by omega⟩
  have hri : row.val+1 = matched.val[candidate]!.val := by dsimp only [row]; omega
  have hci : col.val+1 = target := by dsimp only [col]; omega
  have he : AssignmentScanCut.candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate =
      AssignmentReconstruction.matrix cost n row col - potential n u row - potential n v col := by
    simp only [AssignmentScanCut.candidateCost,reducedAt,alloc.vec.Vec.deref,Slice.from_val,AssignmentReconstruction.matrix,potential,hri,hci]
    rfl
  have hb := henvelope.reduced_bounds hfeasible (cost_bounds cost n) hinitial row col
  rw [he]
  refine ⟨hb.2.1,?_⟩
  unfold reducedBound
  linarith [hb.2.2]

end SubtreeProofs.Rust.AssignmentNumericBounds

end
