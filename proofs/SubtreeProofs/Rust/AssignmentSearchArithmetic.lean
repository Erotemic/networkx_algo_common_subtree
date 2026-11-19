module

public import SubtreeProofs.Rust.AssignmentSafeAdjustment
public import SubtreeProofs.Rust.AssignmentAdjustmentCut
import Mathlib.Tactic

/-!
# Actual safe adjustment directly from the search invariant

The negative reserved column potential is the cumulative adjustment. Feasible
dual accounting bounds it without an extra runtime counter. Attained slack
minima supply all finite slack ranges and subtraction bounds. Consequently
the real source adjustment preserves the numeric and cut invariants with no
caller-supplied local checked-arithmetic range premises.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentSearchArithmetic

open AssignmentColumnScan AssignmentScanInvariant AssignmentScanCut AssignmentAdjustmentInvariant AssignmentAdjustmentLoop
open AssignmentAdjustmentFeasibility AssignmentCutFeasibility AssignmentNumericBounds AssignmentSafeAdjustment AssignmentAdjustmentCut

/-- Independent matrix inequalities, component bounds and exact objective
accounting using the actual reserved slot as the cumulative accumulator. -/
structure PotentialInvariant (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (initialRows : Fin n.val → ℤ)
    (u v : alloc.vec.Vec I128) : Prop where
  envelope : Assignment.Envelope initialRows (potential n u) (potential n v) (-v.val[0]!.val)
  account : Assignment.dualValue (potential n u) (potential n v) =
    Assignment.dualValue initialRows (fun _ => 0) + (-v.val[0]!.val)
  feasible : Assignment.Feasible (AssignmentReconstruction.matrix cost n) (potential n u) (potential n v)

theorem PotentialInvariant.increment_bound (cost : Slice (alloc.vec.Vec I64)) (n : Usize)
    (initialRows : Fin n.val → ℤ) (u v : alloc.vec.Vec I128)
    (h : PotentialInvariant cost n initialRows u v)
    (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude) :
    -v.val[0]!.val ≤ cumulativeBound n.val := by
  have hb := Assignment.total_increment_bound initialRows (potential n u) (potential n v) costMagnitude (-v.val[0]!.val)
    (fun row => (hinitial row).1) (fun row col => (cost_bounds cost n row col).2) h.feasible h.account
  simpa only [Fintype.card_fin,cumulativeBound] using hb

/-- The actual complete adjustment is safe from the independent search
invariants. Every checked-arithmetic range is derived internally. -/
theorem adjust_potentials_from_search_spec (cost : Slice (alloc.vec.Vec I64)) (u v : alloc.vec.Vec I128)
    (matched : Slice Usize) (used : Slice Bool) (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (amount : I128) (n : Usize) (representation : Representation u v matched used slack n)
    (initialRows : Fin n.val → ℤ) (hinitial : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ costMagnitude)
    (hpotential : PotentialInvariant cost n initialRows u v) (hdelta : 0 ≤ amount.val)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hrows : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val ∧ matched.val[col]!.val ≤ n.val)
    (hslacks : SlackInvariant cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched used
      (usedIndices used (n.val+1)) slack predecessor n)
    (hminimum : ∀ target, 0 < target → target ≤ n.val → used.val[target]! = false →
      ∀ candidate ∈ usedIndices used (n.val+1), amount.val ≤
        candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched target candidate) :
    adjust_potentials u v matched used slack amount n ⦃ output =>
      CompleteAdjustment u v matched used slack amount n output ∧
        PotentialInvariant cost n initialRows output.2.1 output.2.2.1 ∧
        SlackInvariant cost (alloc.vec.Vec.deref output.2.1) (alloc.vec.Vec.deref output.2.2.1) matched used
          (usedIndices used (n.val+1)) output.2.2.2 predecessor n ∧
          Bounds u v matched used slack amount n ⦄ := by
  have hcurrentBound := hpotential.increment_bound cost n initialRows u v hinitial
  have hcut := candidate_lower_cut cost u v matched used amount n hminimum
  have hslackBounds : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
      slack.val[col]! = some value → value.val ≤ reducedBound n.val ∧ amount.val ≤ value.val := by
    intro col hb hf value hphysical
    have hp : 0 < col := by
      by_contra hn
      have hz : col = 0 := by omega
      rw [hz,hzero] at hf
      exact Bool.noConfusion hf
    have hm := hslacks col hp hb hf
    have hfinite : slackValue slack.val[col]! ≠ ⊤ := by rw [hphysical]; exact WithTop.coe_ne_top
    obtain ⟨hmember,he⟩ := hm.attained hfinite
    have hvalue : value.val = candidateCost cost (alloc.vec.Vec.deref u) (alloc.vec.Vec.deref v) matched col predecessor.val[col]!.val := by
      rw [hphysical] at he
      exact WithTop.coe_inj.mp he
    have hc := (mem_usedIndices used _ _).mp hmember
    have hcle : predecessor.val[col]!.val ≤ n.val := by omega
    have hr := hrows predecessor.val[col]!.val hcle hc.2
    have hrange := candidate_cost_range cost u v matched n initialRows (-v.val[0]!.val)
      hpotential.envelope hinitial hcurrentBound hpotential.feasible col predecessor.val[col]!.val hp hb hr.1 hr.2
    rw [hvalue]
    exact ⟨hrange.2,hminimum col hp hb hf predecessor.val[col]!.val hmember⟩
  have hreserved : v.val[0]!.val = -(-v.val[0]!.val) := by ring
  have hb := derived_adjustment_bounds cost u v matched used slack amount n representation initialRows (-v.val[0]!.val)
    hinitial hpotential.envelope hpotential.account hreserved hpotential.feasible hdelta hcut hinjective hzero hrows
    (fun col hc hf value hv => (hslackBounds col hc hf value hv).1)
    (fun col hc hf value hv => (hslackBounds col hc hf value hv).2)
  apply WP.spec_mono (adjust_potentials_spec u v matched used slack amount n hb.1)
  intro output hcomplete
  have hnumeric := complete_numeric_invariants u v matched used slack amount n output representation.u_len representation.v_len
    hcomplete initialRows (-v.val[0]!.val) hpotential.envelope hpotential.account hreserved hdelta hinjective hzero hrows
  have hnextIncrement : -output.2.2.1.val[0]!.val = -v.val[0]!.val+amount.val := by rw [hnumeric.2.2]; ring
  refine ⟨hcomplete,?_,?_,hb.1⟩
  · refine ⟨?_,?_,?_⟩
    · rw [hnextIncrement]
      exact hnumeric.1
    · rw [hnextIncrement]
      exact hnumeric.2.1
    · exact complete_feasible u v matched used slack amount n output (AssignmentReconstruction.matrix cost n)
        representation.u_len representation.v_len hcomplete hpotential.feasible hdelta hcut
  · exact complete_slack_invariant cost u v matched used slack predecessor amount n output hb.1 hcomplete hslacks

end SubtreeProofs.Rust.AssignmentSearchArithmetic

end
