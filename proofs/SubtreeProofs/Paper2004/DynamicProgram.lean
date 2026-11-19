module

public import SubtreeProofs.Paper2004.ContractionOracle
public import SubtreeProofs.Paper2004.PaperContainment
public import SubtreeProofs.Paper2004.OptimalEncoding
public import SubtreeProofs.Paper2004.Decomposition

/-!
# The balanced-embedding dynamic program

The proof splits operational contractions according to whether the first pair
survives. The algorithm and its witnesses are independent of the exhaustive
oracle; only the oracle's one-step characterization is used as a structural
lemma about the already independently defined tree relation.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- A single deletion removes the first pair, lies in its interior, or lies in
its suffix. There is no fourth case crossing a balanced-word boundary. -/
theorem dyckContractStep_first_pair (head tail after : DyckWord)
    (step : DyckContractStep (head.nest + tail) after) :
    after = head + tail ∨
      (∃ smaller, after = smaller.nest + tail ∧ DyckContractStep head smaller) ∨
      (∃ smaller, after = head.nest + smaller ∧ DyckContractStep tail smaller) := by
  have ht := contractOnce_complete (dyckContractStep_decodeDyck step)
  simp only [decodeDyck_eq_node_decodeForestDyck, decodeForestDyck_add,
    decodeForestDyck_nest, List.singleton_append, contractOnce] at ht
  obtain ⟨forest, hforest, heq⟩ := List.mem_map.mp ht
  have ha : after = encodeForestDyck forest := by
    have hh := congrArg encodeDyck heq
    simpa only [encodeDyck_decodeDyck, encodeDyck, encodeForestDyck_decodeForestDyck] using hh.symm
  simp only [contractForestOnce, List.mem_append, List.mem_singleton, List.mem_map] at hforest
  rcases hforest with (hsplice | ⟨smaller, hsmall, hforest⟩) | ⟨smaller, hsmall, hforest⟩
  · left
    rw [ha, hsplice]
    simp only [children, encodeForestDyck_append, encodeForestDyck_decodeForestDyck]
  · right; left
    refine ⟨encodeDyck smaller, ?_, ?_⟩
    · rw [ha, ← hforest]
      simp only [encodeForestDyck, encodeForestDyck_decodeForestDyck]
    · have hs := contractStep_encodeDyck (contractOnce_sound hsmall)
      simpa only [encodeDyck, encodeForestDyck_decodeForestDyck] using hs
  · right; right
    refine ⟨encodeForestDyck smaller, ?_, ?_⟩
    · rw [ha, ← hforest]
      simp only [encodeForestDyck, encodeDyck, encodeForestDyck_decodeForestDyck]
    · have hs := contractStep_encodeDyck (contractForestOnce_sound hsmall).atRoot
      simpa only [encodeDyck, encodeForestDyck_decodeForestDyck] using hs

/-- Every operational containment either discards the first pair, or keeps it
and independently contracts its interior and suffix. -/
theorem dyckEmbeds_first_pair {candidate head tail : DyckWord}
    (h : DyckEmbeds candidate (head.nest + tail)) :
    DyckEmbeds candidate (head + tail) ∨
      ∃ inside outside, candidate = inside.nest + outside ∧
        DyckEmbeds inside head ∧ DyckEmbeds outside tail := by
  induction h with
  | refl =>
    exact Or.inr ⟨head, tail, rfl, Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  | @tail middle after hprefix hstep ih =>
    rcases ih with hdropped | ⟨inside, outside, hmiddle, hi, ho⟩
    · exact Or.inl (dyckEmbeds_trans (Relation.ReflTransGen.single hstep) hdropped)
    · rw [hmiddle] at hstep
      rcases dyckContractStep_first_pair inside outside after hstep with
        hdrop | ⟨smaller, hafter, hs⟩ | ⟨smaller, hafter, hs⟩
      · exact Or.inl (hdrop ▸ dyckEmbeds_add hi ho)
      · exact Or.inr ⟨smaller, outside, hafter,
          dyckEmbeds_trans (Relation.ReflTransGen.single hs) hi, ho⟩
      · exact Or.inr ⟨inside, smaller, hafter, hi,
          dyckEmbeds_trans (Relation.ReflTransGen.single hs) ho⟩

/-- Choose a longer balanced word, retaining the first on ties. -/
def longer (first second : DyckWord) : DyckWord :=
  if first.semilength < second.semilength then second else first

@[simp] theorem longer_semilength (first second : DyckWord) :
    (longer first second).semilength = max first.semilength second.semilength := by
  unfold longer
  split <;> omega

/-- Lemma 8 as a constructive recursion, returning a balanced-word witness. -/
def paperCommon (left right : DyckWord) : DyckWord :=
  if _hl : left = 0 then 0 else if _hr : right = 0 then 0 else
    longer (longer
      ((paperCommon left.insidePart right.insidePart).nest +
        paperCommon left.outsidePart right.outsidePart)
      (paperCommon (left.insidePart + left.outsidePart) right))
      (paperCommon left (right.insidePart + right.outsidePart))
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

@[simp] theorem paperCommon_zero_left (right : DyckWord) : paperCommon 0 right = 0 := by
  rw [paperCommon]; simp

@[simp] theorem paperCommon_zero_right (left : DyckWord) : paperCommon left 0 = 0 := by
  rw [paperCommon]; split <;> simp


/-- Structural form of the witness recurrence, useful for representation refinement. -/
theorem paperCommon_nest_add (lh lt rh rt : DyckWord) :
    paperCommon (lh.nest + lt) (rh.nest + rt) =
      longer (longer ((paperCommon lh rh).nest + paperCommon lt rt)
        (paperCommon (lh + lt) (rh.nest + rt)))
        (paperCommon (lh.nest + lt) (rh + rt)) := by
  rw [paperCommon]
  simp only [BalancedDecomposition.nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

/-- Empty is operationally contained in every balanced word. -/
theorem zero_dyckEmbeds (word : DyckWord) : DyckEmbeds 0 word := by
  have h := embeds_encodeDyck (singleton_embeds (decodeDyck word))
  simpa only [encodeDyck_singleton, encodeDyck_decodeDyck] using h

/-- Contracting the first pair is an admissible operational embedding. -/
theorem dyckEmbeds_contract_first {word : DyckWord} (h : word ≠ 0) :
    DyckEmbeds (word.insidePart + word.outsidePart) word := by
  simpa only [zero_add, DyckWord.nest_insidePart_add_outsidePart h] using
    dyckEmbeds_remove 0 word.insidePart word.outsidePart

/-- Choosing between feasible candidates preserves feasibility. -/
theorem commonBalanced_longer {first second left right : DyckWord}
    (hfirst : CommonBalanced first left right) (hsecond : CommonBalanced second left right) :
    CommonBalanced (longer first second) left right := by
  unfold longer
  split
  · exact hsecond
  · exact hfirst

/-- The constructed witness is operationally contained in both inputs. -/
theorem paperCommon_sound (left right : DyckWord) :
    CommonBalanced (paperCommon left right) left right := by
  rw [paperCommon]
  split
  · exact ⟨zero_dyckEmbeds _, zero_dyckEmbeds _⟩
  · rename_i hl
    split
    · exact ⟨zero_dyckEmbeds _, zero_dyckEmbeds _⟩
    · rename_i hr
      have hh := paperCommon_sound left.insidePart right.insidePart
      have ht := paperCommon_sound left.outsidePart right.outsidePart
      apply commonBalanced_longer
      · apply commonBalanced_longer
        · constructor
          · have h := dyckEmbeds_add (dyckEmbeds_context (.nested .hole) hh.1) ht.1
            simpa only [DyckContext.plug, DyckWord.nest_insidePart_add_outsidePart hl] using h
          · have h := dyckEmbeds_add (dyckEmbeds_context (.nested .hole) hh.2) ht.2
            simpa only [DyckContext.plug, DyckWord.nest_insidePart_add_outsidePart hr] using h
        · have h := paperCommon_sound (left.insidePart + left.outsidePart) right
          exact ⟨dyckEmbeds_trans h.1 (dyckEmbeds_contract_first hl), h.2⟩
      · have h := paperCommon_sound left (right.insidePart + right.outsidePart)
        exact ⟨h.1, dyckEmbeds_trans h.2 (dyckEmbeds_contract_first hr)⟩
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- The witness length satisfies precisely Lemma 8's three branches. -/
theorem paperCommon_semilength {left right : DyckWord} (hl : left ≠ 0) (hr : right ≠ 0) :
    (paperCommon left right).semilength = max
      (max ((paperCommon left.insidePart right.insidePart).semilength +
        (paperCommon left.outsidePart right.outsidePart).semilength + 1)
        (paperCommon (left.insidePart + left.outsidePart) right).semilength)
      (paperCommon left (right.insidePart + right.outsidePart)).semilength := by
  rw [paperCommon]
  simp only [hl, hr, ↓reduceDIte, longer_semilength,
    DyckWord.semilength_add, DyckWord.semilength_nest]
  omega

/-- Every independently feasible common word is bounded by the DP witness. -/
theorem paperCommon_upper (left right candidate : DyckWord)
    (h : CommonBalanced candidate left right) :
    candidate.semilength ≤ (paperCommon left right).semilength := by
  by_cases hl : left = 0
  · have hb := dyckEmbeds_semilength_le h.1
    simpa only [hl, DyckWord.semilength_zero, paperCommon_zero_left] using hb
  · by_cases hr : right = 0
    · have hb := dyckEmbeds_semilength_le h.2
      simpa only [hr, DyckWord.semilength_zero, paperCommon_zero_right] using hb
    · rw [paperCommon_semilength hl hr]
      have hleft : DyckEmbeds candidate (left.insidePart.nest + left.outsidePart) := by
        simpa only [DyckWord.nest_insidePart_add_outsidePart hl] using h.1
      have hright : DyckEmbeds candidate (right.insidePart.nest + right.outsidePart) := by
        simpa only [DyckWord.nest_insidePart_add_outsidePart hr] using h.2
      rcases dyckEmbeds_first_pair hleft with hdropped | ⟨inside, outside, hcand, hi, ho⟩
      · have hu := paperCommon_upper (left.insidePart + left.outsidePart) right candidate ⟨hdropped, h.2⟩
        exact hu.trans ((le_max_right _ _).trans (le_max_left _ _))
      · rcases dyckEmbeds_first_pair hright with hdropped | ⟨inside', outside', hcand', hi', ho'⟩
        · have hu := paperCommon_upper left (right.insidePart + right.outsidePart) candidate ⟨h.1, hdropped⟩
          exact hu.trans (le_max_right _ _)
        · have heq : inside.nest + outside = inside'.nest + outside' := hcand.symm.trans hcand'
          have hinside : inside = inside' := by
            have hh := congrArg DyckWord.insidePart heq
            simpa only [DyckWord.insidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest] using hh
          have houtside : outside = outside' := by
            have hh := congrArg DyckWord.outsidePart heq
            simpa only [DyckWord.outsidePart_add DyckWord.nest_ne_zero,
              DyckWord.outsidePart_nest, zero_add] using hh
          have huh := paperCommon_upper left.insidePart right.insidePart inside
            ⟨hi, hinside ▸ hi'⟩
          have hut := paperCommon_upper left.outsidePart right.outsidePart outside
            ⟨ho, houtside ▸ ho'⟩
          apply le_trans _ ((le_max_left _ _).trans (le_max_left _ _))
          rw [hcand, DyckWord.semilength_add, DyckWord.semilength_nest]
          omega
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- General optimality of Lemma 8 under operational containment. -/
theorem paperCommon_correct (left right : DyckWord) :
    IsLongestCommonBalanced (paperCommon left right) left right :=
  ⟨paperCommon_sound left right, fun candidate h => paperCommon_upper left right candidate h⟩

/-- The constructive DP returns an independently maximum common contracted tree. -/
theorem paperCommon_tree_correct (left right : OrderedTree) :
    IsMaximumCommon (decodeDyck (paperCommon left.encodeDyck right.encodeDyck)) left right :=
  longestCommonBalanced_decodes_maximum left right _ (paperCommon_correct _ _)

/-- The numerical paper recurrence is a separate computation from the
independently defined optimum and the witness-producing algorithm. -/
def paperLcs (left right : DyckWord) : Nat :=
  if _hl : left = 0 then 0 else if _hr : right = 0 then 0 else
    max (max (paperLcs left.insidePart right.insidePart +
      paperLcs left.outsidePart right.outsidePart + 1)
      (paperLcs (left.insidePart + left.outsidePart) right))
      (paperLcs left (right.insidePart + right.outsidePart))
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- The independent numerical recurrence agrees with the certified witness. -/
theorem paperLcs_eq_witness (left right : DyckWord) :
    paperLcs left right = (paperCommon left right).semilength := by
  rw [paperLcs]
  split
  · rename_i hl
    simp [hl]
  · rename_i hl
    split
    · rename_i hr
      simp [hr]
    · rename_i hr
      rw [paperCommon_semilength hl hr,
        paperLcs_eq_witness left.insidePart right.insidePart,
        paperLcs_eq_witness left.outsidePart right.outsidePart,
        paperLcs_eq_witness (left.insidePart + left.outsidePart) right,
        paperLcs_eq_witness left (right.insidePart + right.outsidePart)]
termination_by left.semilength + right.semilength
decreasing_by
  all_goals have hl := BalancedDecomposition.contracted_semilength (word := left) (by assumption)
  all_goals have hr := BalancedDecomposition.contracted_semilength (word := right) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Lemma 8 computes the independent maximum, including its attaining witness. -/
theorem paperLcs_optimum (left right : DyckWord) :
    (∃ candidate, CommonBalanced candidate left right ∧ candidate.semilength = paperLcs left right) ∧
      ∀ candidate, CommonBalanced candidate left right → candidate.semilength ≤ paperLcs left right := by
  rw [paperLcs_eq_witness]
  exact ⟨⟨paperCommon left right, paperCommon_sound left right, rfl⟩,
    fun candidate h => paperCommon_upper left right candidate h⟩

end SubtreeProofs.Paper2004.OrderedTree

end
