module

public import SubtreeProofs.Rust.AssignmentColumnScan
import Mathlib.Tactic

/-!
# Exact minimum and prefix invariants for the actual column scan

Mathlib's finite argmin specifies the selected column independently of the
Rust loop. Only positive unused column indices belong to its candidate list.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentScanInvariant

open AssignmentColumnScan

def selectedPrefix (used : Slice Bool) (cursor : Nat) : List Nat :=
  (List.range cursor).filter (fun col => decide (0 < col) && !used.val[col]!)

@[simp] theorem mem_selectedPrefix (used : Slice Bool) (cursor col : Nat) :
    col ∈ selectedPrefix used cursor ↔ col < cursor ∧ 0 < col ∧ used.val[col]! = false := by
  simp [selectedPrefix, Bool.and_eq_true]

@[simp] theorem selectedPrefix_one (used : Slice Bool) : selectedPrefix used 1 = [] := by
  simp [selectedPrefix, List.range_succ]

theorem selectedPrefix_succ (used : Slice Bool) (cursor : Nat) (hcursor : 0 < cursor) :
    selectedPrefix used (cursor+1) =
      if used.val[cursor]! then selectedPrefix used cursor else selectedPrefix used cursor ++ [cursor] := by
  unfold selectedPrefix
  rw [List.range_succ, List.filter_append]
  simp only [List.filter_cons, List.filter_nil]
  cases hc : used.val[cursor]! <;> simp [hcursor]

/-- Link a machine optional minimum and its column to a mathematical argmin. -/
def ArgminLink (weights : Nat → WithTop ℤ) (keys : List Nat) (delta : Option I128) (nextColumn : Usize) : Prop :=
  match keys.argmin weights with
  | none => delta = none
  | some key => ∃ value : I128, delta = some value ∧ nextColumn.val = key ∧ (value.val : WithTop ℤ) = weights key

/-- Strict machine comparison has exactly Mathlib's stable argmin behavior
when appending one newly relaxed column. -/
theorem argminLink_append (weights : Nat → WithTop ℤ) (keys : List Nat)
    (delta : Option I128) (nextColumn : Usize) (best : I128) (candidate : Usize)
    (hlink : ArgminLink weights keys delta nextColumn)
    (hbest : (best.val : WithTop ℤ) = weights candidate.val) :
    ArgminLink weights (keys ++ [candidate.val])
      (chooseDelta delta nextColumn best candidate).1 (chooseDelta delta nextColumn best candidate).2 := by
  unfold ArgminLink at hlink ⊢
  rw [List.argmin_concat]
  cases harg : keys.argmin weights with
  | none =>
    have hd : delta = none := by simpa only [harg] using hlink
    subst delta
    simp only [chooseDelta]
    exact ⟨best, by trivial, by trivial, hbest⟩
  | some key =>
    obtain ⟨old, hd, hnext, hweight⟩ : ∃ value : I128, delta = some value ∧ nextColumn.val = key ∧
        (value.val : WithTop ℤ) = weights key := by simpa only [harg] using hlink
    subst delta
    dsimp only
    have hcompare : weights candidate.val < weights key ↔ best < old := by
      rw [← hbest, ← hweight, WithTop.coe_lt_coe]
      rfl
    by_cases hcmp : best < old
    · rw [ite_eq_left (hcompare.mpr hcmp)]
      simp only [chooseDelta, hcmp, ↓reduceIte]
      exact ⟨best, by trivial, by trivial, hbest⟩
    · rw [ite_eq_right (fun h => hcmp (hcompare.mp h))]
      simp only [chooseDelta, hcmp, ↓reduceIte]
      exact ⟨old, rfl, hnext, hweight⟩

/-- A nonempty processed family has a concrete attaining machine minimum,
whose column is a family member and whose value bounds all its competitors. -/
theorem argminLink_attained (weights : Nat → WithTop ℤ) (keys : List Nat)
    (delta : Option I128) (nextColumn : Usize) (hlink : ArgminLink weights keys delta nextColumn)
    (hne : keys ≠ []) : ∃ value : I128, delta = some value ∧ nextColumn.val ∈ keys ∧
      (value.val : WithTop ℤ) = weights nextColumn.val ∧
      ∀ key ∈ keys, (value.val : WithTop ℤ) ≤ weights key := by
  cases harg : keys.argmin weights with
  | none => exact False.elim (hne (List.argmin_eq_none.mp harg))
  | some key =>
    obtain ⟨value, hd, hnext, hweight⟩ : ∃ value : I128, delta = some value ∧ nextColumn.val = key ∧
        (value.val : WithTop ℤ) = weights key := by simpa only [ArgminLink, harg] using hlink
    have hm : key ∈ keys.argmin weights := by simp [harg]
    refine ⟨value, hd, ?_, ?_, ?_⟩
    · rw [hnext]
      exact List.argmin_mem hm
    · rw [hnext]
      exact hweight
    · intro other ho
      rw [hweight]
      exact List.le_of_mem_argmin ho hm

/-- The strict update test is exactly improvement of the mathematical minimum. -/
theorem improve_iff_min_lt (old : Option I128) (fresh : I128) :
    improve old fresh = true ↔ min (slackValue old) (fresh.val : WithTop ℤ) < slackValue old := by
  cases old with
  | none => simp [improve, slackValue]
  | some previous => simp [improve, slackValue, min_lt_iff, IScalar.lt_equiv]

theorem vec_set_self {T : Type*} [Inhabited T] (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (hindex : index.val < values.length) : (values.set index value).val[index.val]! = value := by
  simp only [alloc.vec.Vec.set_val_eq]
  simp_lists [hindex]

theorem vec_set_other {T : Type*} [Inhabited T] (values : alloc.vec.Vec T) (index : Usize) (value : T)
    (other : Nat) (hother : other < values.length) (hne : index.val ≠ other) :
    (values.set index value).val[other]! = values.val[other]! := by
  simp only [alloc.vec.Vec.set_val_eq]
  simp_lists [hne]

/-- Numerical reduced cost at an ordinary finite column index. -/
def reducedAt (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (activeRow : Usize) (col : Nat) : ℤ :=
  (cost.val[activeRow.val-1]!).val[col-1]!.val - u.val[activeRow.val]!.val - v.val[col]!.val

@[simp] theorem reducedCost_eq_at (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (activeRow candidate : Usize) : reducedCost cost u v activeRow candidate = reducedAt cost u v activeRow candidate.val := rfl

/-- Independent objective for choosing an unused column in this row phase. -/
def columnWeight (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (initialSlack : alloc.vec.Vec (Option I128))
    (activeRow : Usize) (col : Nat) : WithTop ℤ :=
  min (slackValue initialSlack.val[col]!) ((reducedAt cost u v activeRow col : ℤ) : WithTop ℤ)

def SlackPrefix (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (initial current : alloc.vec.Vec (Option I128)) (cursor : Nat) : Prop :=
  current.length = initial.length ∧ ∀ col < initial.length,
    slackValue current.val[col]! = if col ∈ selectedPrefix used cursor then weights col else slackValue initial.val[col]!

def PredecessorPrefix (used : Slice Bool) (weights : Nat → WithTop ℤ) (initialSlack : alloc.vec.Vec (Option I128))
    (initial current : alloc.vec.Vec Usize) (column : Usize) (cursor : Nat) : Prop :=
  current.length = initial.length ∧ ∀ col < initial.length,
    current.val[col]! = if col ∈ selectedPrefix used cursor ∧ weights col < slackValue initialSlack.val[col]!
      then column else initial.val[col]!

@[simp] theorem slackPrefix_one (used : Slice Bool) (weights : Nat → WithTop ℤ) (initial : alloc.vec.Vec (Option I128)) :
    SlackPrefix used weights initial initial 1 := by simp [SlackPrefix]

@[simp] theorem predecessorPrefix_one (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (initialSlack : alloc.vec.Vec (Option I128)) (initial : alloc.vec.Vec Usize) (column : Usize) :
    PredecessorPrefix used weights initialSlack initial initial column 1 := by simp [PredecessorPrefix]

/-- Relaxing the next unused column extends exactly one slot of the prefix;
all other slots retain their independently specified values. -/
theorem slackPrefix_advance (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (initial current : alloc.vec.Vec (Option I128)) (candidate : Usize) (best : I128)
    (hcursor : 0 < candidate.val) (hunused : used.val[candidate.val]! = false)
    (hbound : candidate.val < initial.length) (hprefix : SlackPrefix used weights initial current candidate.val)
    (hbest : (best.val : WithTop ℤ) = weights candidate.val) :
    SlackPrefix used weights initial (current.set candidate (some best)) (candidate.val+1) := by
  rcases hprefix with ⟨hlen,hvalues⟩
  refine ⟨by simpa using hlen, ?_⟩
  intro col hcol
  rw [selectedPrefix_succ used candidate.val hcursor]
  simp only [hunused, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
  by_cases he : col = candidate.val
  · subst col
    rw [vec_set_self current candidate (some best) (by omega)]
    simp [slackValue, hbest]
  · have hget := vec_set_other current candidate (some best) col (by omega) (Ne.symm he)
    rw [hget]
    simpa only [he, or_false] using hvalues col hcol

theorem predecessorAfter_length (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (candidate column : Usize) (fresh : I128) :
    (predecessorAfter slack predecessor candidate column fresh).length = predecessor.length := by
  unfold predecessorAfter
  split <;> simp

/-- The exact strict-improvement predicate determines the new predecessor
slot; all earlier and unprocessed slots retain their specified values. -/
theorem predecessorPrefix_advance (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (initialSlack currentSlack : alloc.vec.Vec (Option I128)) (initial current : alloc.vec.Vec Usize)
    (candidate column : Usize) (fresh : I128)
    (hcursor : 0 < candidate.val) (hunused : used.val[candidate.val]! = false)
    (hbound : candidate.val < initial.length)
    (hprefix : PredecessorPrefix used weights initialSlack initial current column candidate.val)
    (hguard : improve currentSlack.val[candidate.val]! fresh = true ↔
      weights candidate.val < slackValue initialSlack.val[candidate.val]!) :
    PredecessorPrefix used weights initialSlack initial
      (predecessorAfter currentSlack current candidate column fresh) column (candidate.val+1) := by
  rcases hprefix with ⟨hlen,hvalues⟩
  unfold predecessorAfter
  simp only [hguard]
  by_cases hi : weights candidate.val < slackValue initialSlack.val[candidate.val]!
  · rw [ite_eq_left hi]
    refine ⟨by simpa using hlen, ?_⟩
    intro col hcol
    rw [selectedPrefix_succ used candidate.val hcursor]
    simp only [hunused, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
    by_cases he : col = candidate.val
    · subst col
      rw [vec_set_self current candidate column (by omega)]
      simp only [or_true, true_and, hi, ↓reduceIte]
    · rw [vec_set_other current candidate column col (by omega) (Ne.symm he)]
      simpa only [he, or_false] using hvalues col hcol
  · rw [ite_eq_right hi]
    refine ⟨hlen, ?_⟩
    intro col hcol
    rw [selectedPrefix_succ used candidate.val hcursor]
    simp only [hunused, Bool.false_eq_true, ↓reduceIte, List.mem_append, List.mem_singleton]
    by_cases he : col = candidate.val
    · subst col
      have hnot : candidate.val ∉ selectedPrefix used candidate.val := by simp
      simpa only [hi, hnot, or_true, true_and, and_false, false_and, ↓reduceIte] using hvalues candidate.val hbound
    · simpa only [he, or_false] using hvalues col hcol

def LoopInvariant (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (initialSlack : alloc.vec.Vec (Option I128)) (initialPred : alloc.vec.Vec Usize)
    (n activeRow column : Usize) (state : ScanState) : Prop :=
  let weights := columnWeight cost u v initialSlack activeRow
  0 < state.2.2.2.2.val ∧ state.2.2.2.2.val ≤ n.val+1 ∧
    SlackPrefix used weights initialSlack state.1 state.2.2.2.2.val ∧
    PredecessorPrefix used weights initialSlack initialPred state.2.1 column state.2.2.2.2.val ∧
    ArgminLink weights (selectedPrefix used state.2.2.2.2.val) state.2.2.1 state.2.2.2.1

def CompleteScan (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (initialSlack : alloc.vec.Vec (Option I128)) (initialPred : alloc.vec.Vec Usize)
    (n activeRow column : Usize) (output : ScanOutput) : Prop :=
  let weights := columnWeight cost u v initialSlack activeRow
  ∃ value : I128, ∃ selected : Usize, output.1 = core.result.Result.Ok (value,selected) ∧
    SlackPrefix used weights initialSlack output.2.1 (n.val+1) ∧
    PredecessorPrefix used weights initialSlack initialPred output.2.2 column (n.val+1) ∧
    ArgminLink weights (selectedPrefix used (n.val+1)) (some value) selected

/-- The complete actual scan terminates successfully and realizes the
independent prefix updates and finite argmin, under explicit input and
intermediate arithmetic bounds. No minimum or correctness certificate is supplied. -/
theorem scan_columns_spec
    (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (column activeRow n : Usize) (bounds : ScanBounds cost u v used slack predecessor n activeRow)
    (hfits : ∀ candidate : Usize, 0 < candidate.val → candidate.val ≤ n.val → used.val[candidate.val]! = false →
      Fits128 (firstReduced cost u activeRow candidate) ∧ Fits128 (reducedCost cost u v activeRow candidate))
    (havailable : ∃ col : Nat, 0 < col ∧ col ≤ n.val ∧ used.val[col]! = false) :
    scan_columns cost u v used slack predecessor column activeRow n ⦃ output =>
      CompleteScan cost u v used slack predecessor n activeRow column output ⦄ := by
  let weights := columnWeight cost u v slack activeRow
  unfold scan_columns scan_columns_loop
  apply loop.spec_decr_nat (fun state => n.val+1 - state.2.2.2.2.val)
    (LoopInvariant cost u v used slack predecessor n activeRow column)
    (CompleteScan cost u v used slack predecessor n activeRow column) _ _ ?_ ?_
  · rintro ⟨currentSlack,currentPred,delta,nextColumn,cursor⟩ hinv
    rcases hinv with ⟨hpositive,hcursor,hslacks,hpreds,hargmin⟩
    dsimp only at hpositive hcursor hslacks hpreds hargmin ⊢
    by_cases hc : cursor.val ≤ n.val
    · have boundsNow : ScanBounds cost u v used currentSlack currentPred n activeRow :=
        ⟨bounds.n_max, bounds.cost_rows, bounds.row_pos, bounds.row_le, bounds.row_cols,
          bounds.u_len, bounds.v_len, bounds.used_len,
          by rw [hslacks.1]; exact bounds.slack_len,
          by rw [hpreds.1]; exact bounds.predecessor_len⟩
      cases hflag : used.val[cursor.val]! with
      | true =>
        apply WP.spec_mono (body_used_spec cost u v used column activeRow n cursor currentSlack currentPred delta nextColumn
          hc bounds.n_max (lt_of_le_of_lt hc bounds.used_len) hflag)
        rintro output ⟨next,hnext,houtput⟩
        subst output
        dsimp only [LoopInvariant]
        have hkeys : selectedPrefix used next.val = selectedPrefix used cursor.val := by
          rw [hnext, selectedPrefix_succ used cursor.val hpositive]
          simp only [hflag, ↓reduceIte]
        refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, by omega⟩
        · simpa only [SlackPrefix, hkeys] using hslacks
        · simpa only [PredecessorPrefix, hkeys] using hpreds
        · simpa only [hkeys] using hargmin
      | false =>
        have hf := hfits cursor hpositive hc hflag
        apply WP.spec_mono (body_unused_spec cost u v used column activeRow n cursor currentSlack currentPred delta nextColumn
          boundsNow hpositive hc hflag hf.1 hf.2)
        rintro output ⟨fresh,next,hfresh,hnext,houtput⟩
        subst output
        dsimp only [LoopInvariant]
        have hsbound : cursor.val < slack.length := lt_of_le_of_lt hc bounds.slack_len
        have hpbound : cursor.val < predecessor.length := lt_of_le_of_lt hc bounds.predecessor_len
        have hnot : cursor.val ∉ selectedPrefix used cursor.val := by simp
        have hold : slackValue currentSlack.val[cursor.val]! = slackValue slack.val[cursor.val]! := by
          simpa only [hnot, ↓reduceIte] using hslacks.2 cursor.val hsbound
        let best := relaxed currentSlack.val[cursor.val]! fresh
        have hbest : (best.val : WithTop ℤ) = weights cursor.val := by
          calc
            _ = min (slackValue currentSlack.val[cursor.val]!) (fresh.val : WithTop ℤ) := relaxed_value _ _
            _ = _ := by rw [hold, hfresh, reducedCost_eq_at]; rfl
        have hguard : improve currentSlack.val[cursor.val]! fresh = true ↔
            weights cursor.val < slackValue slack.val[cursor.val]! := by
          rw [improve_iff_min_lt, ← relaxed_value, hbest, hold]
        have hs := slackPrefix_advance used weights slack currentSlack cursor best hpositive hflag hsbound hslacks hbest
        have hp := predecessorPrefix_advance used weights slack currentSlack predecessor currentPred cursor column fresh
          hpositive hflag hpbound hpreds hguard
        have ha := argminLink_append weights (selectedPrefix used cursor.val) delta nextColumn best cursor hargmin hbest
        have hkeys : selectedPrefix used next.val = selectedPrefix used cursor.val ++ [cursor.val] := by
          rw [hnext, selectedPrefix_succ used cursor.val hpositive]
          simp only [hflag, Bool.false_eq_true, ↓reduceIte]
        refine ⟨⟨by omega, by omega, ?_, ?_, ?_⟩, by omega⟩
        · simpa only [hnext] using hs
        · simpa only [hnext] using hp
        · simpa only [hkeys] using ha
    · have hstop : n.val < cursor.val := Nat.lt_of_not_ge hc
      have he : cursor.val = n.val+1 := by omega
      obtain ⟨available,hpos,hle,hfree⟩ := havailable
      have hmem : available ∈ selectedPrefix used cursor.val :=
        (mem_selectedPrefix used cursor.val available).mpr ⟨by omega, hpos, hfree⟩
      have hne : selectedPrefix used cursor.val ≠ [] := by intro hempty; simp only [hempty, List.not_mem_nil] at hmem
      obtain ⟨value,hdelta,_,_,_⟩ := argminLink_attained weights (selectedPrefix used cursor.val) delta nextColumn hargmin hne
      rw [hdelta]
      apply WP.spec_mono (body_done_spec cost u v used column activeRow n cursor currentSlack currentPred value nextColumn hstop)
      intro output houtput
      subst output
      dsimp only [CompleteScan]
      refine ⟨value, nextColumn, rfl, ?_, ?_, ?_⟩
      · simpa only [he] using hslacks
      · simpa only [he] using hpreds
      · simpa only [he, hdelta] using hargmin
  · simp [LoopInvariant, ArgminLink]

theorem slackValue_injective : Function.Injective slackValue := by
  intro first second he
  cases first <;> cases second <;> simp_all [slackValue, IScalar.eq_equiv]

/-- Explicit independent optimum and physical attaining entry for the actual
scan. The selected index is positive, unused and inside the matrix dimension. -/
theorem scan_columns_minimum_spec
    (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize)
    (column activeRow n : Usize) (bounds : ScanBounds cost u v used slack predecessor n activeRow)
    (hfits : ∀ candidate : Usize, 0 < candidate.val → candidate.val ≤ n.val → used.val[candidate.val]! = false →
      Fits128 (firstReduced cost u activeRow candidate) ∧ Fits128 (reducedCost cost u v activeRow candidate))
    (havailable : ∃ col : Nat, 0 < col ∧ col ≤ n.val ∧ used.val[col]! = false) :
    scan_columns cost u v used slack predecessor column activeRow n ⦃ output =>
      ∃ value : I128, ∃ selected : Usize,
        output.1 = core.result.Result.Ok (value,selected) ∧ 0 < selected.val ∧ selected.val ≤ n.val ∧
        used.val[selected.val]! = false ∧ output.2.1.val[selected.val]! = some value ∧
        (value.val : WithTop ℤ) = columnWeight cost u v slack activeRow selected.val ∧
        (∀ col, 0 < col → col ≤ n.val → used.val[col]! = false →
          (value.val : WithTop ℤ) ≤ columnWeight cost u v slack activeRow col) ∧
        SlackPrefix used (columnWeight cost u v slack activeRow) slack output.2.1 (n.val+1) ∧
        PredecessorPrefix used (columnWeight cost u v slack activeRow) slack predecessor output.2.2 column (n.val+1) ⦄ := by
  apply WP.spec_mono (scan_columns_spec cost u v used slack predecessor column activeRow n bounds hfits havailable)
  rintro output ⟨value,selected,houtput,hslack,hpred,hlink⟩
  have hne : selectedPrefix used (n.val+1) ≠ [] := by
    obtain ⟨col,hpos,hbound,hflag⟩ := havailable
    have hm := (mem_selectedPrefix used (n.val+1) col).mpr ⟨by omega, hpos, hflag⟩
    intro hempty
    simp only [hempty, List.not_mem_nil] at hm
  obtain ⟨attained, hdelta, hmember, hvalue, hminimum⟩ :=
    argminLink_attained (columnWeight cost u v slack activeRow) _ (some value) selected hlink hne
  have he : value = attained := Option.some.inj hdelta
  subst attained
  have hselected := (mem_selectedPrefix used (n.val+1) selected.val).mp hmember
  have hbound : selected.val ≤ n.val := by omega
  have hphysical : output.2.1.val[selected.val]! = some value := by
    apply slackValue_injective
    have hs := hslack.2 selected.val (lt_of_le_of_lt hbound bounds.slack_len)
    rw [ite_eq_left hmember] at hs
    exact hs.trans hvalue.symm
  refine ⟨value, selected, houtput, hselected.2.1, hbound, hselected.2.2, hphysical, hvalue, ?_, hslack, hpred⟩
  intro col hpos hc hflag
  exact hminimum col ((mem_selectedPrefix used (n.val+1) col).mpr ⟨by omega, hpos, hflag⟩)

end SubtreeProofs.Rust.AssignmentScanInvariant

end
