module

public import SubtreeProofs.Rust.AssignmentPotentialInitialization
public import SubtreeProofs.Shared.AssignmentPotentials
public import Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Sub
import Mathlib.Tactic

/-!
# Refining actual Hungarian column scanning

The Rust scan relaxes minimum slacks and keeps an attaining unused column.
Its scalar values are interpreted as integers; absence means positive infinity.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentColumnScan

abbrev ScanState := alloc.vec.Vec (Option I128) × alloc.vec.Vec Usize × Option I128 × Usize × Usize
abbrev ScanOutput := core.result.Result (I128 × Usize) AssignmentError ×
  alloc.vec.Vec (Option I128) × alloc.vec.Vec Usize

def slackValue : Option I128 → WithTop ℤ
  | none => ⊤
  | some value => (value.val : WithTop ℤ)

def improve (old : Option I128) (fresh : I128) : Bool :=
  match old with
  | none => true
  | some previous => decide (fresh < previous)

def relaxed (old : Option I128) (fresh : I128) : I128 :=
  match old with
  | none => fresh
  | some previous => if fresh < previous then fresh else previous

/-- One relaxation computes the mathematical minimum even for an absent
previous slack. There is no finite sentinel standing for infinity. -/
theorem relaxed_value (old : Option I128) (fresh : I128) :
    ((relaxed old fresh).val : WithTop ℤ) = min (slackValue old) (fresh.val : WithTop ℤ) := by
  cases old with
  | none => simp [relaxed, slackValue]
  | some previous =>
    by_cases h : fresh < previous
    · simp [relaxed, slackValue, h, ← WithTop.coe_min,
        min_eq_right (le_of_lt (show fresh.val < previous.val from h))]
    · simp [relaxed, slackValue, h, ← WithTop.coe_min,
        min_eq_left (le_of_not_gt (show ¬ fresh.val < previous.val from h))]

/-- Checked subtraction returns an exact finite value under its explicit
integer range bounds. These bounds are discharged from potential invariants. -/
theorem checked_sub_spec (x y : I128)
    (hmin : I128.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I128.max) :
    lift (I128.checked_sub x y) ⦃ output => ∃ value, output = some value ∧ value.val = x.val - y.val ⦄ := by
  simp only [lift, WP.spec_ok, I128.checked_sub]
  have h := I128.checked_sub_bv_spec x y
  cases he : core.num.checked_sub_IScalar x y with
  | none =>
    simp only [he] at h
    exact False.elim (h ⟨hmin,hmax⟩)
  | some value =>
    simp only [he] at h
    exact ⟨value, rfl, h.2.2.1⟩

def predecessorAfter (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (candidate column : Usize) (fresh : I128) : alloc.vec.Vec Usize :=
  if improve slack.val[candidate.val]! fresh then predecessor.set candidate column else predecessor

/-- The actual Rust slack helper returns the exact minimum and updates its
predecessor exactly when the new reduced cost strictly improves the old slack. -/
theorem relax_column_spec (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (candidate column : Usize) (fresh : I128)
    (hslack : candidate.val < slack.length) (hpredecessor : candidate.val < predecessor.length) :
    relax_column slack predecessor candidate column fresh ⦃ output =>
      output.1 = relaxed slack.val[candidate.val]! fresh ∧
      output.2.1 = slack.set candidate (some output.1) ∧
      output.2.2 = predecessorAfter slack predecessor candidate column fresh ⦄ := by
  unfold relax_column
  simp only [alloc.vec.Vec.index_slice_index, alloc.vec.Vec.index_mut_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec slack candidate hslack)
  intro old hold
  have hread : old = slack.val[candidate.val]! := by
    simpa only [getElem!_pos slack.val candidate.val hslack] using hold
  cases old with
  | none =>
    dsimp only
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec slack candidate hslack)
    rintro ⟨_,back⟩ ⟨_,hback⟩
    simp only [uncurry_apply_pair]
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec predecessor candidate hpredecessor)
    rintro ⟨_,predBack⟩ ⟨_,hpredBack⟩
    simp [WP.spec_ok, hback, hpredBack, relaxed, predecessorAfter, improve, ← hread]
  | some previous =>
    dsimp only
    by_cases hcmp : fresh < previous
    · rw [ite_eq_left hcmp]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec slack candidate hslack)
      rintro ⟨_,back⟩ ⟨_,hback⟩
      simp only [uncurry_apply_pair]
      apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec predecessor candidate hpredecessor)
      rintro ⟨_,predBack⟩ ⟨_,hpredBack⟩
      simp [WP.spec_ok, hback, hpredBack, relaxed, predecessorAfter, improve, ← hread, hcmp]
    · rw [ite_eq_right hcmp]
      have hOld : slack[candidate]! = some previous := by
        simpa only [alloc.vec.Vec.getElem!_Usize_eq] using hread.symm
      have hset := alloc.vec.Vec.set_getElem!_eq (Option I128) slack candidate
      rw [hOld] at hset
      simp [WP.spec_ok, relaxed, predecessorAfter, improve, ← hread, hcmp, hset]

/-- The helper's returned machine value realizes the independent integer
minimum, with exact tables and no exceptional execution for valid indices. -/
theorem relax_column_minimum_spec (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (candidate column : Usize) (fresh : I128)
    (hslack : candidate.val < slack.length) (hpredecessor : candidate.val < predecessor.length) :
    relax_column slack predecessor candidate column fresh ⦃ output =>
      (output.1.val : WithTop ℤ) = min (slackValue slack.val[candidate.val]!) (fresh.val : WithTop ℤ) ∧
      output.2.1 = slack.set candidate (some output.1) ∧
      output.2.2 = predecessorAfter slack predecessor candidate column fresh ⦄ := by
  apply WP.spec_mono (relax_column_spec slack predecessor candidate column fresh hslack hpredecessor)
  intro output houtput
  refine ⟨?_, houtput.2⟩
  rw [houtput.1]
  exact relaxed_value _ _

/-- Used columns are skipped by the actual source without changing any table
or minimum; the scan cursor advances safely. -/
theorem body_used_spec
    (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (column activeRow n candidate : Usize) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (delta : Option I128) (nextColumn : Usize)
    (hcandidate : candidate.val ≤ n.val) (hn : n.val < Usize.max)
    (hbound : candidate.val < used.length) (hused : used.val[candidate.val]! = true) :
    scan_columns_loop.body cost u v used column activeRow n slack predecessor delta nextColumn candidate
      ⦃ output => ∃ next : Usize, next.val = candidate.val+1 ∧
        output = .cont (slack, predecessor, delta, nextColumn, next) ⦄ := by
  unfold scan_columns_loop.body
  have hc : candidate ≤ n := hcandidate
  rw [ite_eq_left hc]
  apply WP.spec_bind (Slice.index_usize_spec used candidate hbound)
  intro value hvalue
  have he : value = true := by
    rw [hvalue]
    simpa only [getElem!_pos used.val candidate.val hbound] using hused
  simp only [he, ↓reduceIte]
  apply WP.spec_bind (Usize.add_spec (x := candidate) (y := 1#usize) (by have h := hn; scalar_tac))
  intro next hnext
  simp only [WP.spec_ok]
  exact ⟨next, by simpa using hnext, rfl⟩

/-- Once the cursor passes n, a present minimum is returned unchanged. -/
theorem body_done_spec
    (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (column activeRow n candidate : Usize) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (delta : I128) (nextColumn : Usize)
    (hcandidate : n.val < candidate.val) :
    scan_columns_loop.body cost u v used column activeRow n slack predecessor (some delta) nextColumn candidate
      ⦃ output => output = .done (core.result.Result.Ok (delta,nextColumn), slack, predecessor) ⦄ := by
  unfold scan_columns_loop.body
  have hc : ¬ candidate ≤ n := by scalar_tac
  simp [hc]

end SubtreeProofs.Rust.AssignmentColumnScan

end
