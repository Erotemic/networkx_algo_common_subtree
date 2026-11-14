module

public import SubtreeProofs.Rust.AssignmentDriverBody
public import SubtreeProofs.Rust.AssignmentDriverInitialization
public import SubtreeProofs.Rust.AssignmentReturnedSpecification
import Mathlib.Tactic

/-!
# Complete actual assignment driver and optimum reconstruction

Every source iteration adds one covered row. The outer loop terminates with
an independently complete matching, preserved feasible potentials and tight
edges. Actual final reconstruction then returns a globally minimum-cost
permutation with exact cost and exported feasible/tight dual potentials.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentDriverLoop

open AssignmentInitialization AssignmentPotentialInitialization AssignmentSearchInitialization AssignmentSearchArithmetic
open AssignmentAugmentationMatching AssignmentDriverInvariant AssignmentDriverBody AssignmentReturnedSpecification

structure Complete (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (u v : alloc.vec.Vec I128) (matched : alloc.vec.Vec Usize) : Prop where
  u_len : n.val < u.length
  v_len : n.val < v.length
  matched_len : n.val < matched.length
  matching : SubtreeProofs.Assignment.PartialRows n.val n.val (pointers matched)
  potential : PotentialInvariant cost n (initialRows cost n) u v
  matching_tight : SubtreeProofs.Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
    (fun row => u.val[row]!.val) (fun col => v.val[col]!.val) (pointers matched)

def DriverFinished (cost : Slice (alloc.vec.Vec I64)) (n : Usize) (output : DriverOutput) : Prop :=
  let (u,v,matched,failure) := output
  failure = none ∧ Complete cost n u v matched

theorem complete_of_invariant (cost : Slice (alloc.vec.Vec I64)) (n : Usize)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (row : Usize)
    (h : Invariant cost n u v matched predecessor row none) (hr : n.val < row.val) : Complete cost n u v matched := by
  have he : row.val-1 = n.val := by have hb := h.row_bound; omega
  exact ⟨h.u_len,h.v_len,h.matched_len,by simpa only [he] using h.matching,h.potential,h.matching_tight⟩

/-- The complete actual outer loop safely terminates with all rows uniquely
covered. Its row counter provides a strictly decreasing finite measure. -/
theorem finish_assignment_loop_spec (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (input : Input cost n extent)
    (u v : alloc.vec.Vec I128) (matched predecessor : alloc.vec.Vec Usize) (row : Usize) (failure : Option AssignmentError)
    (hinit : Invariant cost n u v matched predecessor row failure) :
    finish_assignment_loop cost n extent u v matched predecessor row failure ⦃ output => DriverFinished cost n output ⦄ := by
  unfold finish_assignment_loop
  apply loop.spec_decr_nat (fun state => n.val+1-state.2.2.2.2.1.val) (StateInvariant cost n)
    (DriverFinished cost n) _ (u,v,matched,predecessor,row,failure) ?_ (by exact hinit)
  rintro ⟨currentU,currentV,currentMatched,currentPred,currentRow,currentFailure⟩ hinv
  change Invariant cost n currentU currentV currentMatched currentPred currentRow currentFailure at hinv
  have hfailure := hinv.failure_none
  subst currentFailure
  by_cases hr : currentRow.val ≤ n.val
  · apply WP.spec_mono (body_running_spec cost n extent input currentU currentV currentMatched currentPred currentRow hinv hr)
    rintro output ⟨next,houtput,hnext,hrow⟩
    subst output
    refine ⟨hnext,?_⟩
    change n.val+1-next.2.2.2.2.1.val < n.val+1-currentRow.val
    omega
  · have hstop : n.val < currentRow.val := Nat.lt_of_not_ge hr
    apply WP.spec_mono (body_done_spec cost n extent currentU currentV currentMatched currentPred currentRow hstop)
    intro output houtput
    subst output
    exact ⟨rfl,complete_of_invariant cost n currentU currentV currentMatched currentPred currentRow hinv hstop⟩

/-- The actual complete Hungarian driver, including constant vector fills,
search, augmentation and decoding, returns an independently optimal assignment
from actual row-minimum initialization. No optimality/result certificate or
local arithmetic-range premise is supplied. -/
theorem finish_assignment_spec (cost : Slice (alloc.vec.Vec I64)) (n extent : Usize) (u : alloc.vec.Vec I128)
    (hn : n.val ≤ U32.max) (hextent : extent.val = n.val+1) (hlen : cost.length = n.val)
    (hsquare : ∀ row ∈ cost.val, row.length = cost.length) (hinit : Initialized cost u cost.length) :
    finish_assignment cost n extent u ⦃ output => ∃ result,
      output = core.result.Result.Ok result ∧ Correct cost n result ⦄ := by
  have input : Input cost n extent := ⟨hn,hextent,hlen,hsquare,initialized_row_bounds cost u n hlen hinit⟩
  unfold finish_assignment
  apply WP.spec_bind (zeros_i128_spec extent)
  intro v hv
  apply WP.spec_bind (zeros_usize_spec extent)
  intro matched hm
  have hdriver := AssignmentDriverInitialization.initial_invariant cost n extent input u v matched matched hinit hv hm hm
  apply WP.spec_bind (finish_assignment_loop_spec cost n extent input u v matched matched 1#usize none hdriver)
  rintro ⟨finalU,finalV,finalMatched,failure⟩ hfinished
  change failure = none ∧ Complete cost n finalU finalV finalMatched at hfinished
  rcases hfinished with ⟨hfailure,hcomplete⟩
  subst failure
  simp only [uncurry_apply_pair]
  have bounds : AssignmentReconstruction.InputBounds cost (alloc.vec.Vec.deref finalU) (alloc.vec.Vec.deref finalV)
      (alloc.vec.Vec.deref finalMatched) n := by
    refine ⟨input.n_max cost n extent,input.n_size,input.cost_len,input.square_at cost n extent,?_,?_,?_⟩
    · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hcomplete.matched_len
    · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hcomplete.u_len
    · simpa only [alloc.vec.Vec.deref,Slice.length,Slice.from_val,alloc.vec.Vec.length] using hcomplete.v_len
  have hfeasible : SubtreeProofs.Assignment.Feasible (AssignmentReconstruction.matrix cost n)
      (AssignmentReconstruction.potential (alloc.vec.Vec.deref finalU) n) (AssignmentReconstruction.potential (alloc.vec.Vec.deref finalV) n) := by
    intro row col
    simpa only [AssignmentReconstruction.potential,AssignmentAdjustmentFeasibility.potential,alloc.vec.Vec.deref,Slice.from_val]
      using hcomplete.potential.feasible row col
  have hmatching : SubtreeProofs.Assignment.PartialRows n.val n.val (fun col => (alloc.vec.Vec.deref finalMatched).val[col]!.val) := by
    have hm := hcomplete.matching
    change SubtreeProofs.Assignment.PartialRows n.val n.val (fun col => finalMatched.val[col]!.val) at hm
    simpa only [alloc.vec.Vec.deref,Slice.from_val] using hm
  have htight : SubtreeProofs.Assignment.TightPointers n.val (AssignmentReconstruction.pointerMatrix cost)
      (fun row => (alloc.vec.Vec.deref finalU).val[row]!.val) (fun col => (alloc.vec.Vec.deref finalV).val[col]!.val)
      (fun col => (alloc.vec.Vec.deref finalMatched).val[col]!.val) := by
    simpa only [SubtreeProofs.Assignment.TightPointers,pointers,alloc.vec.Vec.deref,Slice.from_val] using hcomplete.matching_tight
  apply WP.spec_mono (AssignmentReconstruction.reconstruct_assignment_minimum_spec cost (alloc.vec.Vec.deref finalU) (alloc.vec.Vec.deref finalV)
    (alloc.vec.Vec.deref finalMatched) n bounds hmatching hfeasible htight)
  rintro output ⟨result,assignment,houtput,hrep,hAssignment,_,_⟩
  exact ⟨result,houtput,correct_of_represents cost (alloc.vec.Vec.deref finalU) (alloc.vec.Vec.deref finalV) n assignment result hrep hfeasible hAssignment⟩

end SubtreeProofs.Rust.AssignmentDriverLoop

end
