module

public import SubtreeProofs.Rust.AssignmentRowMinimum
public import SubtreeProofs.Shared.AssignmentDuality
import Mathlib.Tactic

/-!
# Building a feasible Hungarian starting potential

The invariant records independent row minima in processed slots and preserves
the reserved zero slot. The actual Rust loop fills one new slot per iteration.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentPotentialInitialization

open AssignmentInitialization AssignmentRowMinimum

def minimumAt (cost : Slice (alloc.vec.Vec I64)) (row : Nat) : WithTop ℤ :=
  ((cost.val[row]!).val.map IScalar.val).minimum

def Initialized (cost : Slice (alloc.vec.Vec I64)) (potentials : alloc.vec.Vec I128) (count : Nat) : Prop :=
  potentials.length = cost.length + 1 ∧ potentials.val[0]!.val = 0 ∧
    ∀ row < count, (potentials.val[row+1]!.val : WithTop ℤ) = minimumAt cost row

theorem initialized_zero (cost : Slice (alloc.vec.Vec I64)) (potentials : alloc.vec.Vec I128)
    (h : potentials.val = List.replicate (cost.length+1) 0#i128) : Initialized cost potentials 0 := by
  simp [Initialized, h]

/-- Writing the next actual vector slot extends the independently specified
processed-row invariant and preserves every earlier slot. -/
theorem initialized_set (cost : Slice (alloc.vec.Vec I64)) (potentials : alloc.vec.Vec I128)
    (count : Nat) (hcount : count < cost.length) (h : Initialized cost potentials count)
    (index : Usize) (hindex : index.val = count+1) (value : I128)
    (hvalue : (value.val : WithTop ℤ) = minimumAt cost count) :
    Initialized cost (potentials.set index value) (count+1) := by
  rcases h with ⟨hlen, hzero, hrows⟩
  refine ⟨by simpa using hlen, ?_, ?_⟩
  · simp only [alloc.vec.Vec.set_val_eq]
    have hne : index.val ≠ 0 := by omega
    simp_lists [hne]
    simpa only [getElem!_pos potentials.val 0 (show 0 < potentials.val.length by omega)] using hzero
  · intro row hrow
    by_cases he : row = count
    · subst row
      simp only [alloc.vec.Vec.set_val_eq]
      simp_lists [hindex, hlen]
      exact hvalue
    · have hlt : row < count := by omega
      have hne : index.val ≠ row+1 := by omega
      simp only [alloc.vec.Vec.set_val_eq]
      simp_lists [hne]
      simpa only [getElem!_pos potentials.val (row+1) (show row+1 < potentials.val.length by omega)] using hrows row hlt

/-- The actual loop extends the initialized prefix to all rows, never taking
its error branch when every supplied row is nonempty. -/
theorem initial_potentials_loop_spec (cost : Slice (alloc.vec.Vec I64))
    (potentials : alloc.vec.Vec I128) (cursor : Usize)
    (hcursor : cursor.val ≤ cost.length) (hinit : Initialized cost potentials cursor.val)
    (hnonempty : ∀ row ∈ cost.val, row.val ≠ []) :
    initial_potentials_loop cost potentials cursor none ⦃ output =>
      output.2 = none ∧ Initialized cost output.1 cost.length ⦄ := by
  unfold initial_potentials_loop
  apply loop.spec_decr_nat (fun state => cost.length - state.2.1.val)
    (fun state => state.2.1.val ≤ cost.length ∧ state.2.2 = none ∧ Initialized cost state.1 state.2.1.val)
    _ _ _ ?_ ⟨hcursor, rfl, hinit⟩
  rintro ⟨result,row,failure⟩ ⟨hbound,hfailure,hinitialized⟩
  dsimp only at hbound hfailure hinitialized ⊢
  subst failure
  unfold initial_potentials_loop.body
  dsimp only
  split
  · rename_i hlt
    simp only [core.option.Option.is_none]
    have hrow : row.val < cost.length := by scalar_tac
    have hlen := hinitialized.1
    apply WP.spec_bind (Slice.index_usize_spec cost row hrow)
    intro inputRow hinputRow
    have hinput : inputRow = cost.val[row.val]! := by
      simpa only [getElem!_pos cost.val row.val hrow] using hinputRow
    have hmInput : inputRow ∈ cost.val := by
      rw [hinputRow]
      exact List.getElem_mem hrow
    have hn : (alloc.vec.Vec.deref inputRow).val ≠ [] := by
      simpa only [alloc.vec.Vec.deref, Slice.from_val] using hnonempty inputRow hmInput
    apply WP.spec_bind (WP.spec_and (minimum_row_nonempty_spec (alloc.vec.Vec.deref inputRow) hn)
      (minimum_row_spec (alloc.vec.Vec.deref inputRow)))
    rintro output ⟨⟨minimum, houtput, _, _⟩, hminimum⟩
    subst output
    simp only [Std.bind_assoc]
    apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
    intro index hindex
    simp only [alloc.vec.Vec.index_mut_slice_index]
    apply WP.spec_bind (alloc.vec.Vec.index_mut_usize_spec result index (by scalar_tac))
    rintro ⟨_,back⟩ ⟨_,hback⟩
    simp only [uncurry_apply_pair, Std.bind_assoc]
    apply WP.spec_bind (IScalar.cast_inBounds_spec .I128 minimum (by scalar_tac))
    intro widened hwidened
    simp only [bind_ok, hback]
    apply WP.spec_bind (Usize.add_spec (x := row) (y := 1#usize) (by scalar_tac))
    intro next hnext
    simp only [WP.spec_ok]
    refine ⟨⟨by scalar_tac, by trivial, ?_⟩, by scalar_tac⟩
    have hvalue : (widened.val : WithTop ℤ) = minimumAt cost row.val := by
      simp only [toMinimum, alloc.vec.Vec.deref, Slice.from_val] at hminimum
      unfold minimumAt
      rw [← hinput, hwidened]
      exact hminimum
    have hstep := initialized_set cost result row.val hrow hinitialized index (by simpa using hindex) widened hvalue
    simpa only [hnext, UScalar.ofNatCore_val_eq] using hstep
  · rename_i hnot
    simp only [WP.spec_ok]
    have he : row.val = cost.length := by scalar_tac
    exact ⟨True.intro, he ▸ hinitialized⟩

/-- The actual Rust initializer returns a complete row-minimum potential
vector, with no arithmetic, indexing or invariant failure on represented rows. -/
theorem initial_potentials_spec (cost : Slice (alloc.vec.Vec I64)) (extent : Usize)
    (hextent : extent.val = cost.length+1)
    (hnonempty : ∀ row ∈ cost.val, row.val ≠ []) :
    initial_potentials cost extent ⦃ output => ∃ potentials,
      output = core.result.Result.Ok potentials ∧ Initialized cost potentials cost.length ⦄ := by
  unfold initial_potentials
  apply WP.spec_bind (zeros_i128_spec extent)
  intro result hresult
  have hinit : Initialized cost result 0 := initialized_zero cost result (by simpa only [hextent] using hresult)
  apply WP.spec_bind (initial_potentials_loop_spec cost result 0#usize (by simp) hinit hnonempty)
  rintro ⟨final,failure⟩ ⟨hfailure,hfinal⟩
  dsimp only at hfailure hfinal ⊢
  subst failure
  simp only [uncurry_apply_pair, WP.spec_ok]
  exact ⟨final, rfl, hfinal⟩

/-- Independent integer cost matrix on actual row and column indices. -/
def matrix (cost : Slice (alloc.vec.Vec I64)) (row col : Fin cost.length) : ℤ :=
  (cost.val[row.val]!).val[col.val]!.val

def rowPotential (cost : Slice (alloc.vec.Vec I64)) (potentials : alloc.vec.Vec I128)
    (row : Fin cost.length) : ℤ := potentials.val[row.val+1]!.val

/-- Exact row minima imply the independently specified assignment dual
feasibility inequalities with zero column potentials. -/
theorem initialized_feasible (cost : Slice (alloc.vec.Vec I64)) (potentials : alloc.vec.Vec I128)
    (hsquare : ∀ row ∈ cost.val, row.length = cost.length)
    (hinit : Initialized cost potentials cost.length) :
    SubtreeProofs.Assignment.Feasible (matrix cost) (rowPotential cost potentials) (fun _ => 0) := by
  intro row col
  have hrow : cost.val[row.val]! ∈ cost.val := by
    simpa only [getElem!_pos cost.val row.val row.isLt] using List.getElem_mem row.isLt
  have hcol : col.val < (cost.val[row.val]!).val.length := by
    have hlen : (cost.val[row.val]!).val.length = cost.length := hsquare _ hrow
    rw [hlen]
    exact col.isLt
  have hmem : matrix cost row col ∈ (cost.val[row.val]!).val.map IScalar.val := by
    refine List.mem_map.mpr ⟨(cost.val[row.val]!).val[col.val]!, ?_, rfl⟩
    rw [getElem!_pos (cost.val[row.val]!).val col.val hcol]
    exact List.getElem_mem hcol
  have hm := hinit.2.2 row.val row.isLt
  have hle := List.minimum_le_of_mem hmem hm.symm
  simpa only [rowPotential, add_zero] using hle

/-- Successful execution of the real Rust initializer establishes a feasible
starting dual vector for every represented square cost matrix. -/
theorem initial_potentials_feasible_spec (cost : Slice (alloc.vec.Vec I64)) (extent : Usize)
    (hextent : extent.val = cost.length+1)
    (hsquare : ∀ row ∈ cost.val, row.length = cost.length) :
    initial_potentials cost extent ⦃ output => ∃ potentials,
      output = core.result.Result.Ok potentials ∧ Initialized cost potentials cost.length ∧
        SubtreeProofs.Assignment.Feasible (matrix cost) (rowPotential cost potentials) (fun _ => 0) ⦄ := by
  have hnonempty : ∀ row ∈ cost.val, row.val ≠ [] := by
    intro row hr he
    have hn : cost.val ≠ [] := by intro hc; simp only [hc, List.not_mem_nil] at hr
    have hpos : 0 < cost.val.length := List.length_pos_iff.mpr hn
    have hlen : row.val.length = cost.length := hsquare row hr
    rw [he, List.length_nil] at hlen
    change 0 = cost.val.length at hlen
    exact (Nat.ne_of_gt hpos) hlen.symm
  apply WP.spec_mono (initial_potentials_spec cost extent hextent hnonempty)
  rintro output ⟨potentials, rfl, hi⟩
  exact ⟨potentials, rfl, hi, initialized_feasible cost potentials hsquare hi⟩

end SubtreeProofs.Rust.AssignmentPotentialInitialization

end
