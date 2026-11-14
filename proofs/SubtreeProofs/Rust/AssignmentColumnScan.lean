module

public import SubtreeProofs.Rust.AssignmentPotentialInitialization
public import SubtreeProofs.Shared.AssignmentPotentials
public import SubtreeProofs.Rust.AssignmentArithmetic
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
    lift (I128.checked_sub x y) ⦃ output => ∃ value, output = some value ∧ value.val = x.val - y.val ⦄ :=
  AssignmentArithmetic.checked_sub_spec x y hmin hmax

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

def chooseDelta (delta : Option I128) (nextColumn : Usize) (best : I128) (candidate : Usize) : Option I128 × Usize :=
  match delta with
  | none => (some best, candidate)
  | some old => if best < old then (some best, candidate) else (delta,nextColumn)

theorem select_delta_correct (delta : Option I128) (nextColumn : Usize) (best : I128) (candidate : Usize) :
    select_delta delta nextColumn best candidate = .ok (chooseDelta delta nextColumn best candidate) := by
  cases delta with
  | none => rfl
  | some old => by_cases h : best < old <;> simp [select_delta, chooseDelta, h]

theorem chooseDelta_value (delta : Option I128) (nextColumn : Usize) (best : I128) (candidate : Usize) :
    slackValue (chooseDelta delta nextColumn best candidate).1 = min (slackValue delta) (best.val : WithTop ℤ) := by
  calc
    _ = ((relaxed delta best).val : WithTop ℤ) := by
      cases delta with
      | none => rfl
      | some old => by_cases h : best < old <;> simp [chooseDelta, relaxed, slackValue, h]
    _ = _ := relaxed_value delta best

/-- Representation and index bounds for one active row of a scan. -/
structure ScanBounds (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize) (n activeRow : Usize) : Prop where
  n_max : n.val < Usize.max
  cost_rows : n.val ≤ cost.length
  row_pos : 0 < activeRow.val
  row_le : activeRow.val ≤ n.val
  row_cols : n.val ≤ (cost.val[activeRow.val-1]!).length
  u_len : n.val < u.length
  v_len : n.val < v.length
  used_len : n.val < used.length
  slack_len : n.val < slack.length
  predecessor_len : n.val < predecessor.length

def inputCost (cost : Slice (alloc.vec.Vec I64)) (activeRow candidate : Usize) : ℤ :=
  (cost.val[activeRow.val-1]!).val[candidate.val-1]!.val

def firstReduced (cost : Slice (alloc.vec.Vec I64)) (u : Slice I128) (activeRow candidate : Usize) : ℤ :=
  inputCost cost activeRow candidate - u.val[activeRow.val]!.val

def reducedCost (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (activeRow candidate : Usize) : ℤ :=
  firstReduced cost u activeRow candidate - v.val[candidate.val]!.val

def Fits128 (value : ℤ) : Prop := I128.min ≤ value ∧ value ≤ I128.max

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

/-- The unused-column branch performs the exact integer reduced-cost
calculation, relaxes one entry and chooses an attaining minimum. Range bounds
are explicit premises here and will be derived for the complete driver. -/
theorem body_unused_spec
    (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (column activeRow n candidate : Usize) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (delta : Option I128) (nextColumn : Usize)
    (bounds : ScanBounds cost u v used slack predecessor n activeRow)
    (hpositive : 0 < candidate.val) (hcandidate : candidate.val ≤ n.val)
    (hunused : used.val[candidate.val]! = false)
    (hfirst : Fits128 (firstReduced cost u activeRow candidate))
    (hreduced : Fits128 (reducedCost cost u v activeRow candidate)) :
    scan_columns_loop.body cost u v used column activeRow n slack predecessor delta nextColumn candidate
      ⦃ output => ∃ fresh : I128, ∃ next : Usize,
        fresh.val = reducedCost cost u v activeRow candidate ∧ next.val = candidate.val+1 ∧
        let best := relaxed slack.val[candidate.val]! fresh
        let choice := chooseDelta delta nextColumn best candidate
        output = .cont (slack.set candidate (some best),
          predecessorAfter slack predecessor candidate column fresh, choice.1, choice.2, next) ⦄ := by
  rcases bounds with ⟨hn,hcost,hactivePos,hactive,hcols,hu,hv,hused,hslack,hpred⟩
  unfold scan_columns_loop.body
  have hc : candidate ≤ n := hcandidate
  rw [ite_eq_left hc]
  have husedIndex : candidate.val < used.length := lt_of_le_of_lt hcandidate hused
  apply WP.spec_bind (Slice.index_usize_spec used candidate husedIndex)
  intro usedValue hUsedValue
  have heUsed : usedValue = false := by
    rw [hUsedValue]
    simpa only [getElem!_pos used.val candidate.val husedIndex] using hunused
  simp only [heUsed, Bool.false_eq_true, ↓reduceIte]
  apply WP.spec_bind (Usize.sub_spec (x := activeRow) (y := 1#usize) (by scalar_tac))
  intro rowIndex hRowIndex
  have hrowIndex : rowIndex.val = activeRow.val-1 := by simpa using hRowIndex.1
  have hrowBound : rowIndex.val < cost.length := by scalar_tac
  apply WP.spec_bind (Slice.index_usize_spec cost rowIndex hrowBound)
  intro costRow hCostRow
  have hinput : costRow = cost.val[activeRow.val-1]! := by
    rw [← hrowIndex, getElem!_pos cost.val rowIndex.val hrowBound]
    exact hCostRow
  apply WP.spec_bind (Usize.sub_spec (x := candidate) (y := 1#usize) (by scalar_tac))
  intro colIndex hColIndex
  have hcolIndex : colIndex.val = candidate.val-1 := by simpa using hColIndex.1
  have hcostCols : n.val ≤ costRow.length := by simpa only [hinput] using hcols
  have hcolBound : colIndex.val < costRow.length := by scalar_tac
  simp only [alloc.vec.Vec.index_slice_index]
  apply WP.spec_bind (alloc.vec.Vec.index_usize_spec costRow colIndex hcolBound)
  intro costValue hCostValue
  have hcostValue : costValue.val = inputCost cost activeRow candidate := by
    unfold inputCost
    rw [← hinput, ← hcolIndex, getElem!_pos costRow.val colIndex.val hcolBound]
    exact congrArg IScalar.val hCostValue
  apply WP.spec_bind (IScalar.cast_inBounds_spec .I128 costValue (by scalar_tac))
  intro widened hWidened
  have huIndex : activeRow.val < u.length := lt_of_le_of_lt hactive hu
  apply WP.spec_bind (Slice.index_usize_spec u activeRow huIndex)
  intro uValue hUValue
  have huValue : uValue.val = u.val[activeRow.val]!.val := by
    simpa only [getElem!_pos u.val activeRow.val huIndex] using congrArg IScalar.val hUValue
  have hlowFirst : I128.min ≤ widened.val - uValue.val := by
    rw [hWidened, hcostValue, huValue]
    exact hfirst.1
  have hhighFirst : widened.val - uValue.val ≤ I128.max := by
    rw [hWidened, hcostValue, huValue]
    exact hfirst.2
  apply WP.spec_bind (checked_sub_spec widened uValue hlowFirst hhighFirst)
  rintro firstOption ⟨first, hFirstOption, hFirst⟩
  subst firstOption
  simp only
  have hvIndex : candidate.val < v.length := lt_of_le_of_lt hcandidate hv
  apply WP.spec_bind (Slice.index_usize_spec v candidate hvIndex)
  intro vValue hVValue
  have hvValue : vValue.val = v.val[candidate.val]!.val := by
    simpa only [getElem!_pos v.val candidate.val hvIndex] using congrArg IScalar.val hVValue
  have hfirstValue : first.val = firstReduced cost u activeRow candidate := by
    simp only [hFirst, hWidened, hcostValue, huValue, firstReduced]
  have hlowReduced : I128.min ≤ first.val - vValue.val := by
    rw [hfirstValue, hvValue]
    exact hreduced.1
  have hhighReduced : first.val - vValue.val ≤ I128.max := by
    rw [hfirstValue, hvValue]
    exact hreduced.2
  apply WP.spec_bind (checked_sub_spec first vValue hlowReduced hhighReduced)
  rintro reducedOption ⟨fresh, hReducedOption, hFresh⟩
  subst reducedOption
  simp only
  apply WP.spec_bind (relax_column_spec slack predecessor candidate column fresh
    (lt_of_le_of_lt hcandidate hslack) (lt_of_le_of_lt hcandidate hpred))
  rintro ⟨best,newSlack,newPred⟩ ⟨hBest,hSlack,hPred⟩
  dsimp only at hBest hSlack hPred ⊢
  simp only [uncurry_apply_pair]
  rcases hChoice : chooseDelta delta nextColumn best candidate with ⟨newDelta,newColumn⟩
  rw [select_delta_correct, hChoice, bind_ok]
  simp only [uncurry_apply_pair]
  apply WP.spec_bind (Usize.add_spec (x := candidate) (y := 1#usize) (by have h := hn; scalar_tac))
  intro next hNext
  simp only [WP.spec_ok]
  refine ⟨fresh, next, ?_, by simpa using hNext, ?_⟩
  · simp only [hFresh, hfirstValue, hvValue, reducedCost]
  · have hChoiceCanonical := hChoice
    rw [hBest] at hChoiceCanonical
    simp only [hSlack, hPred, hBest, hChoiceCanonical]

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
