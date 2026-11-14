module

public import SubtreeProofs.Rust.AssignmentAdjustmentFeasibility
import Mathlib.Tactic

/-!
# Actual cut cardinality, objective progress, and the reserved accumulator

An injective family of positive matched rows, including the reserved column
zero, gives one more selected real row than selected real columns. The actual
potential update raises the independent dual objective by its adjustment and
subtracts that same amount from the reserved column potential.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustmentProgress

open AssignmentColumnScan AssignmentAdjustment AssignmentAdjustmentInvariant AssignmentAdjustmentLoop AssignmentAdjustmentFeasibility

theorem realIndex_injective (n : Usize) : Function.Injective (fun index : Fin n.val => index.val+1) := by
  intro first second he
  dsimp only at he
  apply Fin.ext
  omega

theorem selectedColumns_image (n : Usize) (used : Slice Bool) :
    (selectedColumns n used).image (fun col => col.val+1) = (usedIndices used (n.val+1)).erase 0 := by
  ext index
  constructor
  · intro hmem
    obtain ⟨col,hcol,he⟩ := Finset.mem_image.mp hmem
    apply Finset.mem_erase.mpr
    refine ⟨by omega, ?_⟩
    subst index
    exact (mem_selectedColumns n used col).mp hcol
  · intro hmem
    obtain ⟨hne,hused⟩ := Finset.mem_erase.mp hmem
    have hi := (mem_usedIndices used (n.val+1) index).mp hused
    have hfin : index-1 < n.val := by omega
    refine Finset.mem_image.mpr ⟨⟨index-1,hfin⟩, ?_, by dsimp; omega⟩
    apply (mem_selectedColumns n used _).mpr
    have he : index-1+1 = index := by omega
    simpa only [he] using hused

theorem selectedRows_image (n : Usize) (matched : Slice Usize) (used : Slice Bool)
    (hpositive : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val)
    (hbound : ∀ col, col ≤ n.val → used.val[col]! = true → matched.val[col]!.val ≤ n.val) :
    (selectedRows n matched used).image (fun row => row.val+1) = usedRows matched used (n.val+1) := by
  ext index
  constructor
  · intro hmem
    obtain ⟨row,hrow,he⟩ := Finset.mem_image.mp hmem
    subst index
    exact (mem_selectedRows n matched used row).mp hrow
  · intro hmem
    obtain ⟨col,hcol,hused,he⟩ := (mem_usedRows matched used (n.val+1) index).mp hmem
    have hc : col ≤ n.val := by omega
    have hpos := hpositive col hc hused
    have hle := hbound col hc hused
    have hfin : index-1 < n.val := by omega
    refine Finset.mem_image.mpr ⟨⟨index-1,hfin⟩, ?_, by dsimp; omega⟩
    apply (mem_selectedRows n matched used _).mpr
    have heIndex : index-1+1 = index := by omega
    rw [heIndex]
    exact (mem_usedRows matched used (n.val+1) index).mpr ⟨col,hcol,hused,he⟩

/-- Counting actual used pointers, with the reserved zero column, establishes
exactly the cardinality premise needed by independent dual progress. -/
theorem selected_cardinality (n : Usize) (matched : Slice Usize) (used : Slice Bool)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hpositive : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val)
    (hbound : ∀ col, col ≤ n.val → used.val[col]! = true → matched.val[col]!.val ≤ n.val) :
    (selectedRows n matched used).card = (selectedColumns n used).card+1 := by
  have hrowimage := selectedRows_image n matched used hpositive hbound
  have hcolimage := selectedColumns_image n used
  have hrowcard := Finset.card_image_of_injOn (s := selectedRows n matched used)
    (Set.injOn_of_injective (realIndex_injective n))
  have hcolcard := Finset.card_image_of_injOn (s := selectedColumns n used)
    (Set.injOn_of_injective (realIndex_injective n))
  have hpointers : (usedRows matched used (n.val+1)).card = (usedIndices used (n.val+1)).card := by
    apply Finset.card_image_of_injOn
    intro first hfirst second hsecond he
    have hf := (mem_usedIndices used (n.val+1) first).mp hfirst
    have hs := (mem_usedIndices used (n.val+1) second).mp hsecond
    exact hinjective first (by omega) hf.2 second (by omega) hs.2 he
  have hzeroMem : 0 ∈ usedIndices used (n.val+1) := (mem_usedIndices used _ _).mpr ⟨by omega,hzero⟩
  have herase := Finset.card_erase_add_one hzeroMem
  rw [hrowimage] at hrowcard
  rw [hcolimage] at hcolcard
  omega

/-- Objective progress is proved for the actual returned machine vectors. -/
theorem complete_dual_progress (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (hu : n.val < u.length) (hv : n.val < v.length)
    (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (hinjective : UsedInjective matched used n) (hzero : used.val[0]! = true)
    (hpositive : ∀ col, col ≤ n.val → used.val[col]! = true → 0 < matched.val[col]!.val)
    (hbound : ∀ col, col ≤ n.val → used.val[col]! = true → matched.val[col]!.val ≤ n.val) :
    Assignment.dualValue (potential n output.2.1) (potential n output.2.2.1) =
      Assignment.dualValue (potential n u) (potential n v) + amount.val := by
  rw [frames_rows u v _ _ matched used slack _ amount n hu hcomplete.2,
    frames_columns u v _ _ matched used slack _ amount n hv hcomplete.2]
  exact Assignment.adjust_dualValue_one _ _ _ _ amount.val
    (selected_cardinality n matched used hinjective hzero hpositive hbound)

/-- Slot zero records the negative cumulative potential adjustment. -/
theorem complete_reserved_column (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput)
    (hv : n.val < v.length) (hcomplete : CompleteAdjustment u v matched used slack amount n output)
    (hzero : used.val[0]! = true) :
    output.2.2.1.val[0]!.val = v.val[0]!.val-amount.val := by
  have hmem : 0 ∈ usedIndices used (n.val+1) := (mem_usedIndices used _ _).mpr ⟨by omega,hzero⟩
  simpa only [columnExpected, hmem, ↓reduceIte] using hcomplete.2.2.1.2 0 (by omega)

end SubtreeProofs.Rust.AssignmentAdjustmentProgress

end
