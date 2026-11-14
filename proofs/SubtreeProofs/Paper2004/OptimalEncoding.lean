module

public import SubtreeProofs.Paper2004.ContractionCompleteness

/-!
# Optimality under the tree / balanced-word correspondence

This is the optimization claim of Theorem 2 with operational pair deletion.
The literal least interpretation of printed Definition 2 is treated separately
by the counterexample module.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- A common balanced word under independent operational containment. -/
def CommonBalanced (candidate first second : DyckWord) : Prop :=
  DyckEmbeds candidate first ∧ DyckEmbeds candidate second

/-- Maximal semilength among all common operationally contained words. -/
def IsLongestCommonBalanced (candidate first second : DyckWord) : Prop :=
  CommonBalanced candidate first second ∧
    ∀ other, CommonBalanced other first second → other.semilength ≤ candidate.semilength

/-- Encoding preserves the independently specified optimum, in both directions. -/
theorem isMaximumCommon_iff_isLongestCommonBalanced (candidate first second : OrderedTree) :
    IsMaximumCommon candidate first second ↔
      IsLongestCommonBalanced candidate.encodeDyck first.encodeDyck second.encodeDyck := by
  constructor
  · intro h
    constructor
    · exact ⟨embeds_encodeDyck h.1.1, embeds_encodeDyck h.1.2⟩
    · intro other hother
      have hleft : Embeds (decodeDyck other) first := by
        simpa only [decodeDyck_encodeDyck] using dyckEmbeds_decodeDyck hother.1
      have hright : Embeds (decodeDyck other) second := by
        simpa only [decodeDyck_encodeDyck] using dyckEmbeds_decodeDyck hother.2
      have hbound := h.2 (decodeDyck other) ⟨hleft, hright⟩
      have hsize : (decodeDyck other).edgeCount = other.semilength := by
        simpa only [encodeDyck_decodeDyck] using (encodeDyck_semilength (decodeDyck other)).symm
      simpa only [hsize, encodeDyck_semilength] using hbound
  · intro h
    constructor
    · exact ⟨embeds_iff_dyckEmbeds.mpr h.1.1, embeds_iff_dyckEmbeds.mpr h.1.2⟩
    · intro other hother
      have hbound := h.2 other.encodeDyck
        ⟨embeds_encodeDyck hother.1, embeds_encodeDyck hother.2⟩
      simpa only [encodeDyck_semilength] using hbound

/-- Theorem 2: decode any longest common operational balanced word to obtain
an independently maximum common embedded tree. -/
theorem longestCommonBalanced_decodes_maximum
    (first second : OrderedTree) (candidate : DyckWord)
    (h : IsLongestCommonBalanced candidate first.encodeDyck second.encodeDyck) :
    IsMaximumCommon (decodeDyck candidate) first second := by
  apply (isMaximumCommon_iff_isLongestCommonBalanced _ _ _).mpr
  simpa only [encodeDyck_decodeDyck] using h

end SubtreeProofs.Paper2004.OrderedTree

end
