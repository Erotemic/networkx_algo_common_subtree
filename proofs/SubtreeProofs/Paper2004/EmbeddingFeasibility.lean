module

public import SubtreeProofs.Paper2004.DynamicProgram
import Mathlib.Tactic

/-! # Memoized common-shape equality decides complete pattern containment -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- Equal semilength under operational pair deletion permits no deletion. -/
theorem DyckEmbeds.eq_of_semilength_eq {small large : DyckWord} (h : DyckEmbeds small large)
    (he : small.semilength = large.semilength) : small = large := by
  induction h with
  | refl => rfl
  | @tail middle after hp hs ih =>
    have hbefore := dyckEmbeds_semilength_le hp
    have hdrop := (dyckContractStep_decodeDyck hs).edgeCount_decreases
    simp only [edgeCount_decodeDyck] at hdrop
    omega

/-- The certified common word is the entire pattern precisely when the
independent contraction relation admits that pattern. This uses optimum
completeness and strict deletion size, rather than any reconstruction algorithm. -/
theorem paperCommon_eq_left_iff (pattern input : DyckWord) :
    paperCommon pattern input = pattern ↔ DyckEmbeds pattern input := by
  constructor
  · intro he
    simpa only [he] using (paperCommon_sound pattern input).2
  · intro he
    have hs := (paperCommon_sound pattern input).1
    have hlo := paperCommon_upper pattern input pattern ⟨Relation.ReflTransGen.refl,he⟩
    have hhi := dyckEmbeds_semilength_le hs
    exact hs.eq_of_semilength_eq (by omega)

end SubtreeProofs.Paper2004.OrderedTree

end
