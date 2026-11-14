module

public import SubtreeProofs.Rust.AssignmentAdjustmentInvariant
import Mathlib.Tactic

/-!
# The complete actual potential-adjustment loop

The result specifies every slot of all three returned vectors. Used-pointer
injectivity and explicit integer ranges are input properties; neither an
optimality certificate nor a claim about the loop's result is assumed.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentAdjustmentLoop

open AssignmentColumnScan AssignmentScanInvariant AssignmentAdjustment AssignmentAdjustmentInvariant

structure Bounds (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) : Prop where
  n_max : n.val < Usize.max
  matched_len : n.val < matched.length
  used_len : n.val < used.length
  v_len : n.val < v.length
  slack_len : n.val < slack.length
  row_bound : ∀ col, col ≤ n.val → used.val[col]! = true → matched.val[col]!.val < u.length
  injective : UsedInjective matched used n
  row_fits : ∀ col, col ≤ n.val → used.val[col]! = true →
    Fits128 (u.val[matched.val[col]!.val]!.val + amount.val)
  column_fits : ∀ col, col ≤ n.val → used.val[col]! = true → Fits128 (v.val[col]!.val - amount.val)
  slack_fits : ∀ col, col ≤ n.val → used.val[col]! = false → ∀ value : I128,
    slack.val[col]! = some value → Fits128 (value.val-amount.val)

def Frames (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (cursor : Nat)
    (currentU currentV : alloc.vec.Vec I128) (currentSlack : alloc.vec.Vec (Option I128)) : Prop :=
  Frame u currentU IScalar.val (rowExpected u matched used amount cursor) ∧
  Frame v currentV IScalar.val (columnExpected v used amount cursor) ∧
  Frame slack currentSlack slackValue (slackExpected slack used amount cursor)

def LoopInvariant (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (state : AdjustState) : Prop :=
  state.2.2.2.val ≤ n.val+1 ∧ Frames u v matched used slack amount state.2.2.2.val state.1 state.2.1 state.2.2.1

def CompleteAdjustment (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize) (output : AdjustOutput) : Prop :=
  output.1 = core.result.Result.Ok () ∧
    Frames u v matched used slack amount (n.val+1) output.2.1 output.2.2.1 output.2.2.2

/-- The actual Rust loop terminates without an indexing or checked-arithmetic
failure and realizes the independently defined simultaneous adjustment. -/
theorem adjust_potentials_spec (u v : alloc.vec.Vec I128) (matched : Slice Usize) (used : Slice Bool)
    (slack : alloc.vec.Vec (Option I128)) (amount : I128) (n : Usize)
    (bounds : Bounds u v matched used slack amount n) :
    adjust_potentials u v matched used slack amount n ⦃ output =>
      CompleteAdjustment u v matched used slack amount n output ⦄ := by
  unfold adjust_potentials adjust_potentials_loop
  apply loop.spec_decr_nat (fun state => n.val+1-state.2.2.2.val)
    (LoopInvariant u v matched used slack amount n)
    (CompleteAdjustment u v matched used slack amount n) _ _ ?_ ?_
  · rintro ⟨currentU,currentV,currentSlack,cursor⟩ hinv
    rcases hinv with ⟨hcursor, hu,hv,hs⟩
    dsimp only at hcursor hu hv hs ⊢
    by_cases hc : cursor.val ≤ n.val
    · have hused := lt_of_le_of_lt hc bounds.used_len
      have hmatched := lt_of_le_of_lt hc bounds.matched_len
      have hvbound := lt_of_le_of_lt hc bounds.v_len
      have hsbound := lt_of_le_of_lt hc bounds.slack_len
      cases hflag : used.val[cursor.val]! with
      | true =>
        have hrowbound := bounds.row_bound cursor.val hc hflag
        have hnot := assigned_not_processed matched used n cursor.val bounds.injective hc hflag
        have huold : currentU.val[matched.val[cursor.val]!.val]!.val = u.val[matched.val[cursor.val]!.val]!.val := by
          simpa only [rowExpected, hnot, ↓reduceIte, add_zero] using hu.2 _ hrowbound
        have hvold : currentV.val[cursor.val]!.val = v.val[cursor.val]!.val := by
          have hnotcol : cursor.val ∉ usedIndices used cursor.val := by simp
          simpa only [columnExpected, hnotcol, ↓reduceIte, sub_zero] using hv.2 _ hvbound
        apply WP.spec_mono (body_used_spec matched used amount n cursor currentU currentV currentSlack
          hc bounds.n_max hused hmatched (by rw [hv.1]; exact hvbound)
          (by rw [hu.1]; exact hrowbound) hflag
          (by rw [huold]; exact bounds.row_fits cursor.val hc hflag)
          (by rw [hvold]; exact bounds.column_fits cursor.val hc hflag))
        rintro output ⟨rowValue,colValue,next,hrow,hcol,hnext,houtput⟩
        subst output
        dsimp only [LoopInvariant, Frames]
        refine ⟨⟨by omega, ?_, ?_, ?_⟩, by omega⟩
        · rw [hnext]
          apply frame_set u currentU IScalar.val _ _ matched.val[cursor.val]! rowValue hu hrowbound
          · rw [rowExpected_used u matched used amount cursor.val _ hflag]
            simpa only [ite_true] using hrow.trans (congrArg (fun value : ℤ => value+amount.val) huold)
          · intro other _ hne
            rw [rowExpected_used u matched used amount cursor.val _ hflag]
            exact ite_eq_right hne
        · rw [hnext]
          apply frame_set v currentV IScalar.val _ _ cursor colValue hv hvbound
          · rw [columnExpected_used v used amount cursor.val _ hflag]
            simpa only [ite_true] using hcol.trans (congrArg (fun value : ℤ => value-amount.val) hvold)
          · intro other _ hne
            rw [columnExpected_used v used amount cursor.val _ hflag]
            exact ite_eq_right hne
        · rw [hnext]
          exact frame_unchanged slack currentSlack slackValue _ _ hs
            (fun col _ => slackExpected_used slack used amount cursor.val col hflag)
      | false =>
        have hold := slackFrame_unprocessed slack currentSlack used amount cursor.val hsbound hs
        have hrows := frame_unchanged u currentU IScalar.val _ _ hu
          (fun row _ => rowExpected_unused u matched used amount cursor.val row hflag)
        have hcols := frame_unchanged v currentV IScalar.val _ _ hv
          (fun col _ => columnExpected_unused v used amount cursor.val col hflag)
        cases hpresent : currentSlack.val[cursor.val]! with
        | none =>
          apply WP.spec_mono (body_unused_none_spec matched used amount n cursor currentU currentV currentSlack
            hc bounds.n_max hused (by rw [hs.1]; exact hsbound) hflag hpresent)
          rintro output ⟨next,hnext,houtput⟩
          subst output
          dsimp only [LoopInvariant, Frames]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          rw [hnext]
          exact ⟨hrows,hcols,slackFrame_none slack currentSlack used amount cursor.val hsbound hs hflag hpresent⟩
        | some old =>
          have hfit := bounds.slack_fits cursor.val hc hflag old (hold.symm.trans hpresent)
          apply WP.spec_mono (body_unused_some_spec matched used amount n cursor currentU currentV currentSlack old
            hc bounds.n_max hused (by rw [hs.1]; exact hsbound) hflag hpresent hfit)
          rintro output ⟨value,next,hvalue,hnext,houtput⟩
          subst output
          dsimp only [LoopInvariant, Frames]
          refine ⟨⟨by omega, ?_⟩, by omega⟩
          rw [hnext]
          exact ⟨hrows,hcols,slackFrame_some slack currentSlack used amount cursor old value hsbound hs hflag hpresent hvalue⟩
    · have hstop : n.val < cursor.val := Nat.lt_of_not_ge hc
      have he : cursor.val = n.val+1 := by omega
      apply WP.spec_mono (body_done_spec matched used amount n cursor currentU currentV currentSlack hstop)
      intro output houtput
      subst output
      dsimp only [CompleteAdjustment, Frames]
      exact ⟨rfl, by simpa only [he] using hu, by simpa only [he] using hv, by simpa only [he] using hs⟩
  · simp [LoopInvariant, Frames, Frame, rowExpected, columnExpected, slackExpected, usedRows, usedIndices]

end SubtreeProofs.Rust.AssignmentAdjustmentLoop

end
