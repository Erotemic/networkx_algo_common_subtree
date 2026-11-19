module

public import SubtreeProofs.Rust.MatchingDecoding
import Mathlib.Tactic

/-!
# Exact membership and uniqueness of the decoded indexed witness

The decoder model's list membership is an independent coordinate condition:
a real row, a real right column, its actual assignment index, and a positive
compatible original weight. Distinct loop row indices make the list unique.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.MatchingDecodedWitness

open MatchingCostSpecification MatchingDecoding

theorem decodedAt_some (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize)
    (row : Nat) (pair : Nat × Nat) : decodedAt weights left right columns row = some pair ↔
      pair.1 = row ∧ pair.2 < right ∧ columns.val[row]!.val = left+pair.2 ∧
        0 < ((weightValue (weights.val[row]!).val[pair.2]!).getD 0) := by
  unfold decodedAt
  dsimp only
  by_cases hg : left ≤ columns.val[row]!.val ∧ columns.val[row]!.val-left < right ∧
      0 < ((weightValue (weights.val[row]!).val[columns.val[row]!.val-left]!).getD 0)
  · rw [ite_eq_left hg]
    constructor
    · intro he
      have hp := Option.some.inj he
      have hf : pair.1 = row := congrArg Prod.fst hp.symm
      have hs : pair.2 = columns.val[row]!.val-left := congrArg Prod.snd hp.symm
      refine ⟨hf,?_,?_,?_⟩
      · rw [hs]
        exact hg.2.1
      · rw [hs]
        omega
      · rw [hs]
        exact hg.2.2
    · rintro ⟨hf,_,hc,_⟩
      apply congrArg some
      apply Prod.ext hf.symm
      dsimp only
      omega
  · rw [ite_eq_right hg]
    simp only [reduceCtorEq,false_iff]
    rintro ⟨_,hb,hc,hp⟩
    apply hg
    have hs : columns.val[row]!.val-left = pair.2 := by omega
    refine ⟨by omega,?_,?_⟩
    · rw [hs]
      exact hb
    · rw [hs]
      exact hp

/-- Exact natural input-index membership of the decoder's finite list. -/
theorem mem_decodedPrefix (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize)
    (count : Nat) (pair : Nat × Nat) : pair ∈ decodedPrefix weights left right columns count ↔
      pair.1 < count ∧ pair.2 < right ∧ columns.val[pair.1]!.val = left+pair.2 ∧
        0 < ((weightValue (weights.val[pair.1]!).val[pair.2]!).getD 0) := by
  constructor
  · intro hm
    obtain ⟨row,hr,he⟩ := List.mem_filterMap.mp hm
    obtain ⟨hf,hb,hc,hp⟩ := (decodedAt_some weights left right columns row pair).mp he
    rw [← hf] at hr hc hp
    exact ⟨List.mem_range.mp hr,hb,hc,hp⟩
  · rintro ⟨hr,hb,hc,hp⟩
    exact List.mem_filterMap.mpr ⟨pair.1,List.mem_range.mpr hr,
      (decodedAt_some weights left right columns pair.1 pair).mpr ⟨rfl,hb,hc,hp⟩⟩

/-- The actual witness view has no duplicated coordinate pair; this is a
list property, so finite-set conversion cannot conceal duplicate output. -/
theorem decodedPrefix_nodup (weights : Slice (alloc.vec.Vec (Option I64))) (left right : Nat) (columns : Slice Usize)
    (count : Nat) : (decodedPrefix weights left right columns count).Nodup := by
  induction count with
  | zero => simp [decodedPrefix]
  | succ count ih =>
    rw [decodedPrefix_succ]
    cases he : decodedAt weights left right columns count with
    | none => simpa only [Option.toList_none,List.append_nil] using ih
    | some pair =>
      simp only [Option.toList_some]
      have hf := ((decodedAt_some weights left right columns count pair).mp he).1
      have hnot : pair ∉ decodedPrefix weights left right columns count := by
        intro hm
        have hb := ((mem_decodedPrefix weights left right columns count pair).mp hm).1
        omega
      apply List.nodup_append.mpr
      refine ⟨ih,by simp,?_⟩
      intro first hfirst second hsecond heq
      have hs : second = pair := List.mem_singleton.mp hsecond
      exact hnot (heq.trans hs ▸ hfirst)

end SubtreeProofs.Rust.MatchingDecodedWitness

end
