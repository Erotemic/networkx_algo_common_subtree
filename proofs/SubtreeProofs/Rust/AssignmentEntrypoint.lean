module

public import SubtreeProofs.Rust.AssignmentDriverLoop
public import SubtreeProofs.Rust.AssignmentValidation
public import Aeneas.Std.Scalar.CheckedOps.Add
import Mathlib.Tactic

/-!
# Total correctness of the actual public exact assignment API

Every represented matrix returns either an independently optimal assignment
with exact feasible/tight exported potentials, or precisely the documented
size/shape error. Accepted inputs cannot produce arithmetic or invariant
errors. The proof executes actual validation, initialization and the full
source driver; it assumes no optimum or program-result certificate.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentEntrypoint

open AssignmentValidation AssignmentPotentialInitialization AssignmentDriverLoop AssignmentReturnedSpecification

def Admissible (cost : Slice (alloc.vec.Vec I64)) : Prop :=
  cost.length ≤ U32.max ∧ cost.length < Usize.max ∧ Square cost

/-- Exact success and error contract for the actual public API. -/
def ResultSpec (cost : Slice (alloc.vec.Vec I64)) (output : core.result.Result verified_assignment_core.Assignment AssignmentError) : Prop :=
  match output with
  | .Ok result => Admissible cost ∧ Correct cost (Slice.len cost) result
  | .Err error =>
    (error = .TooLarge ∧ (U32.max < cost.length ∨ Usize.max ≤ cost.length)) ∨
    (error = .NonSquare ∧ cost.length ≤ U32.max ∧ cost.length < Usize.max ∧ ¬ Square cost)

/-- The pinned public unsigned checked-add theorem directly specifies its
actual alias, so no private-body bridge is required here. -/
theorem checked_extent_spec (n : Usize) :
    lift (Usize.checked_add n 1#usize) ⦃ output =>
      match output with
      | none => Usize.max < n.val+1
      | some extent => extent.val = n.val+1 ⦄ := by
  simp only [lift,WP.spec_ok]
  have h := Usize.checked_add_bv_spec n 1#usize
  cases he : Usize.checked_add n 1#usize with
  | none => simpa only [he,UScalar.ofNatCore_val_eq] using h
  | some extent =>
    simp only [he] at h
    simpa only [UScalar.ofNatCore_val_eq] using h.2.1

theorem u32_max_value : core.num.U32.MAX.val = U32.max := by
  norm_num [core.num.U32.MAX,UScalar.ofNat,UScalar.ofNatCore_val_eq,U32.rMax,U32.max_eq]

theorem u32_max_fits_usize : core.num.U32.MAX.val ≤ UScalar.max .Usize := by
  rw [u32_max_value,UScalar.max_USize_eq]
  rcases Usize.bounds_eq with he | he
  · rw [he]
  · rw [he]
    scalar_tac

/-- Total correctness of the real public Rust entry point, on every
represented input, including early size/shape rejection and empty input. -/
theorem min_cost_assignment_total_spec (cost : Slice (alloc.vec.Vec I64)) :
    min_cost_assignment cost ⦃ output => ResultSpec cost output ⦄ := by
  let n := Slice.len cost
  have hn : n.val = cost.length := Slice.len_val cost
  unfold min_cost_assignment
  apply WP.spec_bind (UScalar.cast_inBounds_spec .Usize core.num.U32.MAX u32_max_fits_usize)
  intro limit hLimit
  have hlimit : limit.val = U32.max := hLimit.trans u32_max_value
  split
  · rename_i hlarge
    have hlargeValue : U32.max < cost.length := by scalar_tac
    simp only [WP.spec_ok,ResultSpec]
    exact Or.inl ⟨True.intro,Or.inl hlargeValue⟩
  · rename_i hnotLarge
    have hsmall : n.val ≤ U32.max := by scalar_tac
    apply WP.spec_bind (checked_extent_spec n)
    intro extentOption hExtent
    cases extentOption with
    | none =>
      simp only [WP.spec_ok,ResultSpec]
      exact Or.inl ⟨True.intro,Or.inr (by omega)⟩
    | some extent =>
      have hextent : extent.val = n.val+1 := hExtent
      have hcapacity : n.val < Usize.max := by scalar_tac
      apply WP.spec_bind (is_square_spec cost)
      intro square hSquare
      cases square with
      | false =>
        have hnot : ¬ Square cost := by
          intro hs
          exact Bool.noConfusion (hSquare.mpr hs)
        simp only [Bool.false_eq_true,↓reduceIte,WP.spec_ok,ResultSpec]
        exact Or.inr ⟨True.intro,by omega,by omega,hnot⟩
      | true =>
        have hsquare : Square cost := hSquare.mp rfl
        have hshape : ∀ row ∈ cost.val, row.length = cost.length := hsquare
        apply WP.spec_bind (initial_potentials_feasible_spec cost extent (by omega) hshape)
        rintro initialized ⟨u,hInitialized,hinit,_⟩
        subst initialized
        apply WP.spec_mono (finish_assignment_spec cost n extent u hsmall hextent hn.symm hshape hinit)
        rintro output ⟨result,houtput,hcorrect⟩
        subst output
        exact ⟨⟨by omega,by omega,hsquare⟩,hcorrect⟩

/-- Every admitted square signed-integer matrix succeeds with an independent
minimum-cost permutation and exact primal/dual output data. -/
theorem min_cost_assignment_spec (cost : Slice (alloc.vec.Vec I64)) (haccepted : Admissible cost) :
    min_cost_assignment cost ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ Correct cost (Slice.len cost) result ⦄ := by
  apply WP.spec_mono (min_cost_assignment_total_spec cost)
  intro output houtput
  cases output with
  | Ok result => exact ⟨result,rfl,houtput.2⟩
  | Err error =>
    rcases houtput with ⟨_,hlarge⟩ | ⟨_,_,_,hshape⟩
    · rcases haccepted with ⟨hs,hc,_⟩
      rcases hlarge with hl | hl <;> omega
    · exact False.elim (hshape haccepted.2.2)

end SubtreeProofs.Rust.AssignmentEntrypoint

end
