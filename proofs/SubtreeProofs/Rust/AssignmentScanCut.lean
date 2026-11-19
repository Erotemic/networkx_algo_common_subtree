module

public import SubtreeProofs.Rust.AssignmentScanInvariant
public import SubtreeProofs.Shared.AssignmentSlack
import Mathlib.Tactic

/-!
# Actual column scanning extends the independent cut minimum invariant

Each candidate column names a row via the unchanged matching pointers. A
stored finite minimum has an attaining predecessor in the candidate set;
all candidate reduced costs bound it from above. The actual source scan
adds its active column to that set, including exact tie behavior.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentScanCut

open AssignmentColumnScan AssignmentScanInvariant

def candidateCost (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128)
    (matched : Slice Usize) (target candidate : Nat) : ℤ :=
  reducedAt cost u v matched.val[candidate]! target

def SlackInvariant (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize)
    (used : Slice Bool) (candidates : Finset Nat) (slack : alloc.vec.Vec (Option I128))
    (predecessor : alloc.vec.Vec Usize) (n : Usize) : Prop :=
  ∀ target, 0 < target → target ≤ n.val → used.val[target]! = false →
    Assignment.MinimumAt (candidateCost cost u v matched target) candidates
      (slackValue slack.val[target]!) predecessor.val[target]!.val

/-- The exact whole-table scan frames imply the independent minimum and
attaining-predecessor invariant for the enlarged cut. -/
theorem frames_extend_cut (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize)
    (used : Slice Bool) (candidates : Finset Nat)
    (slack newSlack : alloc.vec.Vec (Option I128)) (predecessor newPred : alloc.vec.Vec Usize)
    (column n : Usize) (hslen : n.val < slack.length) (hplen : n.val < predecessor.length)
    (hinvariant : SlackInvariant cost u v matched used candidates slack predecessor n)
    (hslack : SlackPrefix used (columnWeight cost u v slack matched.val[column.val]!) slack newSlack (n.val+1))
    (hpred : PredecessorPrefix used (columnWeight cost u v slack matched.val[column.val]!) slack predecessor newPred column (n.val+1)) :
    SlackInvariant cost u v matched used (insert column.val candidates) newSlack newPred n := by
  intro target hp hb hf
  have hmem : target ∈ selectedPrefix used (n.val+1) := (mem_selectedPrefix used _ _).mpr ⟨by omega,hp,hf⟩
  have hs := hslack.2 target (lt_of_le_of_lt hb hslen)
  have ht := hpred.2 target (lt_of_le_of_lt hb hplen)
  have heSlack : slackValue newSlack.val[target]! =
      min (slackValue slack.val[target]!) ((candidateCost cost u v matched target column.val : ℤ) : WithTop ℤ) := by
    simpa only [hmem,↓reduceIte,columnWeight,candidateCost] using hs
  have hePred : newPred.val[target]!.val =
      if (candidateCost cost u v matched target column.val : WithTop ℤ) < slackValue slack.val[target]!
      then column.val else predecessor.val[target]!.val := by
    dsimp only [candidateCost]
    by_cases hcmp : (reducedAt cost u v matched.val[column.val]! target : WithTop ℤ) < slackValue slack.val[target]!
    all_goals simpa only [hmem,true_and,columnWeight,min_lt_iff,lt_irrefl,false_or,hcmp,↓reduceIte] using congrArg UScalar.val ht
  rw [heSlack,hePred]
  exact (hinvariant target hp hb hf).insert column.val

/-- The actual scan returns an attained global cut adjustment and extends the
candidate invariant. The predecessor at the selected column identifies an
actual cut edge attaining the chosen amount. -/
theorem scan_columns_cut_spec (cost : Slice (alloc.vec.Vec I64)) (u v : Slice I128) (matched : Slice Usize)
    (used : Slice Bool) (candidates : Finset Nat)
    (slack : alloc.vec.Vec (Option I128)) (predecessor : alloc.vec.Vec Usize) (column n : Usize)
    (bounds : ScanBounds cost u v used slack predecessor n matched.val[column.val]!)
    (hfits : ∀ candidate : Usize, 0 < candidate.val → candidate.val ≤ n.val → used.val[candidate.val]! = false →
      Fits128 (firstReduced cost u matched.val[column.val]! candidate) ∧ Fits128 (reducedCost cost u v matched.val[column.val]! candidate))
    (havailable : ∃ col : Nat, 0 < col ∧ col ≤ n.val ∧ used.val[col]! = false)
    (hinvariant : SlackInvariant cost u v matched used candidates slack predecessor n) :
    scan_columns cost u v used slack predecessor column matched.val[column.val]! n ⦃ output =>
      ∃ amount : I128, ∃ selected : Usize,
        output.1 = core.result.Result.Ok (amount,selected) ∧ 0 < selected.val ∧ selected.val ≤ n.val ∧
        used.val[selected.val]! = false ∧ output.2.1.val[selected.val]! = some amount ∧
        SlackInvariant cost u v matched used (insert column.val candidates) output.2.1 output.2.2 n ∧
        output.2.2.val[selected.val]!.val ∈ insert column.val candidates ∧
        amount.val = candidateCost cost u v matched selected.val output.2.2.val[selected.val]!.val ∧
        SlackPrefix used (columnWeight cost u v slack matched.val[column.val]!) slack output.2.1 (n.val+1) ∧
        PredecessorPrefix used (columnWeight cost u v slack matched.val[column.val]!) slack predecessor output.2.2 column (n.val+1) ∧
        ∀ target, 0 < target → target ≤ n.val → used.val[target]! = false →
          ∀ candidate ∈ insert column.val candidates, amount.val ≤ candidateCost cost u v matched target candidate ⦄ := by
  apply WP.spec_mono (scan_columns_minimum_spec cost u v used slack predecessor column matched.val[column.val]! n bounds hfits havailable)
  rintro output ⟨amount,selected,houtput,hp,hb,hfree,hphysical,hvalue,hminimum,hslack,hpred⟩
  have hnew := frames_extend_cut cost u v matched used candidates slack output.2.1 predecessor output.2.2 column n
    bounds.slack_len bounds.predecessor_len hinvariant hslack hpred
  have hselected := hnew selected.val hp hb hfree
  have hfinite : slackValue output.2.1.val[selected.val]! ≠ ⊤ := by rw [hphysical]; exact WithTop.coe_ne_top
  obtain ⟨hmember,hattained⟩ := hselected.attained hfinite
  have hatt : amount.val = candidateCost cost u v matched selected.val output.2.2.val[selected.val]!.val := by
    rw [hphysical] at hattained
    exact WithTop.coe_inj.mp hattained
  refine ⟨amount,selected,houtput,hp,hb,hfree,hphysical,hnew,hmember,hatt,hslack,hpred,?_⟩
  intro target htp htb htf candidate hcandidate
  have hmem : target ∈ selectedPrefix used (n.val+1) := (mem_selectedPrefix used _ _).mpr ⟨by omega,htp,htf⟩
  have hs := hslack.2 target (lt_of_le_of_lt htb bounds.slack_len)
  rw [ite_eq_left hmem] at hs
  apply WithTop.coe_le_coe.mp
  calc
    (amount.val : WithTop ℤ) ≤ columnWeight cost u v slack matched.val[column.val]! target := hminimum target htp htb htf
    _ = slackValue output.2.1.val[target]! := hs.symm
    _ ≤ (candidateCost cost u v matched target candidate : WithTop ℤ) := (hnew target htp htb htf).lower candidate hcandidate

end SubtreeProofs.Rust.AssignmentScanCut

end
