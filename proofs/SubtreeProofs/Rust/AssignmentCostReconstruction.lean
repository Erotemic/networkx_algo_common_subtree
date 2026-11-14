module

public import SubtreeProofs.Rust.AssignmentInverseReconstruction
public import SubtreeProofs.Rust.AssignmentArithmetic
import Mathlib.Tactic

/-!
# Actual reconstruction of assignment cost and exported potentials

The running total is an independent integer prefix sum of the selected input
costs. Signed i64 bounds and the accepted dimension imply every checked i128
addition succeeds. Exported potentials are exact prefixes of the input vectors
after omitting reserved slot zero.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentCostReconstruction

open AssignmentColumnScan AssignmentScanInvariant AssignmentInverseReconstruction

def inputAt (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) (row : Nat) : ℤ :=
  (cost.val[row]!).val[columns.val[row]!.val]!.val

def prefixCost (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) (count : Nat) : ℤ :=
  ∑ row ∈ Finset.range count, inputAt cost columns row

theorem prefixCost_zero (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) :
    prefixCost cost columns 0 = 0 := by simp [prefixCost]

theorem prefixCost_succ (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) (count : Nat) :
    prefixCost cost columns (count+1) = prefixCost cost columns count + inputAt cost columns count := by
  exact Finset.sum_range_succ _ _

theorem inputAt_bounds (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) (row : Nat) :
    -(2^63 : ℤ) ≤ inputAt cost columns row ∧ inputAt cost columns row ≤ (2^63 : ℤ) := by
  unfold inputAt
  scalar_tac

theorem prefixCost_bounds (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize) (count : Nat) :
    -(count : ℤ)*2^63 ≤ prefixCost cost columns count ∧ prefixCost cost columns count ≤ (count : ℤ)*2^63 := by
  induction count with
  | zero => simp [prefixCost_zero]
  | succ count ih =>
    rw [prefixCost_succ]
    have hentry := inputAt_bounds cost columns count
    push_cast
    constructor <;> linarith

/-- No selected-cost prefix can overflow i128 at the accepted dimension,
including arbitrary mixtures of the two extreme signed i64 values. -/
theorem prefixCost_fits (cost : Slice (alloc.vec.Vec I64)) (columns : alloc.vec.Vec Usize)
    (count : Nat) (hcount : count ≤ U32.max) : Fits128 (prefixCost cost columns count) := by
  have hb := prefixCost_bounds cost columns count
  constructor <;> scalar_tac

structure Bounds (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (columns : alloc.vec.Vec Usize) (n : Usize) : Prop where
  n_max : n.val < Usize.max
  n_size : n.val ≤ U32.max
  cost_len : cost.length = n.val
  square : ∀ row < n.val, (cost.val[row]!).length = n.val
  columns_len : columns.length = n.val
  columns_bound : ∀ row < n.val, columns.val[row]!.val < n.val
  u_len : n.val < u.length
  v_len : n.val < v.length

abbrev CostState := Option AssignmentError × I128 × alloc.vec.Vec I128 × alloc.vec.Vec I128 × Usize
abbrev CostOutput := Option AssignmentError × I128 × alloc.vec.Vec I128 × alloc.vec.Vec I128

/-- Exact source-level row lookup, widening, checked sum, potential copies
and cursor increment for one successful reconstruction iteration. -/
theorem body_step_spec (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (columns : alloc.vec.Vec Usize) (n index : Usize) (total : I128)
    (rowPot colPot : alloc.vec.Vec I128) (bounds : Bounds cost u v columns n)
    (hi : index.val < n.val) (hr : rowPot.length < Usize.max) (hv : colPot.length < Usize.max)
    (hfit : Fits128 (total.val + inputAt cost columns index.val)) :
    reconstruct_assignment_loop1.body cost u v n columns none total rowPot colPot index ⦃ output =>
      ∃ value : I128, ∃ next : Usize, ∃ newRows newCols : alloc.vec.Vec I128,
        value.val = total.val + inputAt cost columns index.val ∧ next.val = index.val+1 ∧
        newRows.val = rowPot.val++[u.val[next.val]!] ∧ newCols.val = colPot.val++[v.val[next.val]!] ∧
        output = .cont (none,value,newRows,newCols,next) ⦄ := by
  unfold reconstruct_assignment_loop1.body
  have hindex : index < n := hi
  simp only [hindex,↓reduceIte,core.option.Option.is_none]
  apply WP.spec_bind (Slice.index_usize_spec cost index (by rw [bounds.cost_len]; exact hi))
  intro inputRow hInputRow
  have hrow : inputRow = cost.val[index.val]! := by
    simpa only [getElem!_pos cost.val index.val (by rw [← bounds.cost_len] at hi; exact hi)] using hInputRow
  simp only [alloc.vec.Vec.index_slice_index]
  have hic : index.val < columns.length := by rw [bounds.columns_len]; exact hi
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec columns index hic)
  intro selected hSelected
  have hselected : selected = columns.val[index.val]! := by
    simpa only [getElem!_pos columns.val index.val hic] using hSelected
  have hcol : selected.val < inputRow.length := by
    rw [hrow,bounds.square index.val hi,hselected]
    exact bounds.columns_bound index.val hi
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec inputRow selected hcol)
  intro entry hEntry
  have hentry : entry.val = inputAt cost columns index.val := by
    rw [hEntry,← getElem!_pos inputRow.val selected.val hcol,hrow,hselected]
    rfl
  apply WP.spec_bind (IScalar.cast_inBounds_spec .I128 entry (by scalar_tac))
  intro widened hWidened
  apply WP.spec_bind (AssignmentArithmetic.checked_add_spec total widened
    (by rw [hWidened,hentry]; exact hfit.1) (by rw [hWidened,hentry]; exact hfit.2))
  rintro valueOption ⟨value,hValueOption,hValue⟩
  subst valueOption
  simp only [bind_ok,uncurry_apply_pair]
  apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
  intro next hNext
  have hnext : next.val = index.val+1 := by simpa using hNext
  have hnu : next.val < u.length := by have h := bounds.u_len; omega
  have hnv : next.val < v.length := by have h := bounds.v_len; omega
  apply WP.spec_bind (Slice.index_usize_spec u next hnu)
  intro rowValue hRowValue
  apply WP.spec_bind (alloc.vec.Vec.push_spec rowPot rowValue hr)
  intro newRows hRows
  apply WP.spec_bind (Slice.index_usize_spec v next hnv)
  intro colValue hColValue
  apply WP.spec_bind (alloc.vec.Vec.push_spec colPot colValue hv)
  intro newCols hCols
  simp only [WP.spec_ok]
  refine ⟨value,next,newRows,newCols,by simpa only [hWidened,hentry] using hValue,hnext,?_,?_,rfl⟩
  · simpa only [hRowValue,getElem!_pos u.val next.val hnu] using hRows
  · simpa only [hColValue,getElem!_pos v.val next.val hnv] using hCols


/-- The exact list of real potential entries, without reserved slot zero. -/
def potentialPrefix (values : Slice I128) (count : Nat) : List I128 :=
  (List.range count).map (fun index => values.val[index+1]!)

@[simp] theorem potentialPrefix_length (values : Slice I128) (count : Nat) :
    (potentialPrefix values count).length = count := by simp [potentialPrefix]

theorem potentialPrefix_succ (values : Slice I128) (count : Nat) :
    potentialPrefix values (count+1) = potentialPrefix values count ++ [values.val[count+1]!] := by
  simp only [potentialPrefix,List.range_succ,List.map_append,List.map_cons,List.map_nil]

/-- The actual second reconstruction loop terminates successfully, computes
an independent selected-cost sum and copies the precise real potentials.
Its checked-arithmetic safety follows from signed input and dimension bounds. -/
theorem reconstruct_cost_loop_spec (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (columns : alloc.vec.Vec Usize) (n : Usize) (bounds : Bounds cost u v columns n) :
    reconstruct_assignment_loop1 cost u v n none columns 0#i128
      (alloc.vec.Vec.new I128) (alloc.vec.Vec.new I128) 0#usize ⦃ output =>
        output.1 = none ∧ output.2.1.val = prefixCost cost columns n.val ∧
          output.2.2.1.val = potentialPrefix u n.val ∧ output.2.2.2.val = potentialPrefix v n.val ⦄ := by
  unfold reconstruct_assignment_loop1
  apply loop.spec_decr_nat (fun state => n.val-state.2.2.2.2.val)
    (fun (state : CostState) => state.1 = none ∧ state.2.2.2.2.val ≤ n.val ∧
      state.2.1.val = prefixCost cost columns state.2.2.2.2.val ∧
      state.2.2.1.val = potentialPrefix u state.2.2.2.2.val ∧
      state.2.2.2.1.val = potentialPrefix v state.2.2.2.2.val)
    (fun (output : CostOutput) => output.1 = none ∧ output.2.1.val = prefixCost cost columns n.val ∧
      output.2.2.1.val = potentialPrefix u n.val ∧ output.2.2.2.val = potentialPrefix v n.val) _ _ ?_ ?_
  · rintro ⟨failure,total,rows,cols,index⟩ ⟨hfailure,hindex,htotal,hrows,hcols⟩
    dsimp only at hfailure hindex htotal hrows hcols ⊢
    subst failure
    by_cases hi : index.val < n.val
    · have hrlen : rows.length = index.val := by
        change rows.val.length = index.val
        rw [hrows,potentialPrefix_length]
      have hclen : cols.length = index.val := by
        change cols.val.length = index.val
        rw [hcols,potentialPrefix_length]
      have hfit : Fits128 (total.val + inputAt cost columns index.val) := by
        rw [htotal,← prefixCost_succ]
        exact prefixCost_fits cost columns (index.val+1) (by have h := bounds.n_size; omega)
      apply WP.spec_mono (body_step_spec cost u v columns n index total rows cols bounds hi
        (by rw [hrlen]; have h := bounds.n_max; omega) (by rw [hclen]; have h := bounds.n_max; omega) hfit)
      rintro output ⟨value,next,newRows,newCols,hvalue,hnext,hnewRows,hnewCols,houtput⟩
      subst output
      refine ⟨⟨rfl,by dsimp; omega,?_,?_,?_⟩,by dsimp; omega⟩
      · dsimp only
        simpa only [hnext,htotal,prefixCost_succ] using hvalue
      · dsimp only
        simpa only [hnext,hrows,potentialPrefix_succ] using hnewRows
      · dsimp only
        simpa only [hnext,hcols,potentialPrefix_succ] using hnewCols
    · unfold reconstruct_assignment_loop1.body
      have hnot : ¬ index < n := by scalar_tac
      simp only [hnot,↓reduceIte,WP.spec_ok]
      have he : index.val = n.val := by omega
      exact ⟨True.intro,by simpa only [he] using htotal,by simpa only [he] using hrows,by simpa only [he] using hcols⟩
  · simp [prefixCost_zero,potentialPrefix]

end SubtreeProofs.Rust.AssignmentCostReconstruction

end
