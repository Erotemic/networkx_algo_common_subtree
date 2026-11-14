module

public import SubtreeProofs.Rust.Generated.VerifiedOrderedCore
public import SubtreeProofs.Paper2004.DynamicProgram

/-!
# Refinement of the maintained Rust ordered solver

The Rust binary pair grammar is interpreted in independently specified Dyck
words, then decoded to the ordered-tree specification. Generated recursive
programs retain their actual Aeneas partial-fixpoint semantics.
-/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.OrderedSolver

open Paper2004.OrderedTree

/-- Interpret a Rust structural word without using any Rust solver. -/
def toDyck : BalancedWord → DyckWord
  | .Empty => 0
  | .Pair head tail => (toDyck head).nest + toDyck tail


/-- Every independent Dyck word has a value in the Rust structural grammar. -/
def fromDyck (word : DyckWord) : BalancedWord :=
  if _h : word = 0 then .Empty else .Pair (fromDyck word.insidePart) (fromDyck word.outsidePart)
termination_by word.semilength
decreasing_by
  all_goals have hc := Paper2004.BalancedDecomposition.contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

@[simp] theorem toDyck_fromDyck (word : DyckWord) : toDyck (fromDyck word) = word := by
  rw [fromDyck]
  split
  · rename_i h
    exact h.symm
  · rename_i h
    change (toDyck (fromDyck word.insidePart)).nest + toDyck (fromDyck word.outsidePart) = word
    rw [toDyck_fromDyck word.insidePart, toDyck_fromDyck word.outsidePart]
    exact DyckWord.nest_insidePart_add_outsidePart h
termination_by word.semilength
decreasing_by
  all_goals have hc := Paper2004.BalancedDecomposition.contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

@[simp] theorem fromDyck_toDyck (word : BalancedWord) : fromDyck (toDyck word) = word := by
  induction word with
  | Empty => rw [fromDyck]; rfl
  | Pair head tail ihHead ihTail =>
    rw [fromDyck]
    simp only [toDyck, Paper2004.BalancedDecomposition.nest_add_ne_zero, ↓reduceDIte,
      DyckWord.insidePart_add DyckWord.nest_ne_zero,
      DyckWord.outsidePart_add DyckWord.nest_ne_zero,
      DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add, ihHead, ihTail]

/-- Mathematical structural concatenation on the representation type. -/
def appendWord : BalancedWord → BalancedWord → BalancedWord
  | .Empty, right => right
  | .Pair head tail, right => .Pair head (appendWord tail right)

@[simp] theorem toDyck_appendWord (left right : BalancedWord) :
    toDyck (appendWord left right) = toDyck left + toDyck right := by
  induction left with
  | Empty => simp [appendWord, toDyck]
  | Pair head tail _ ih => simp [appendWord, toDyck, ih, add_assoc]

/-- Real translated Rust copying terminates and returns the same value. -/
theorem copy_word_correct (word : BalancedWord) : copy_word word = .ok word := by
  induction word with
  | Empty => rw [copy_word]
  | Pair head tail ihHead ihTail =>
    rw [copy_word, ihHead, bind_ok, ihTail, bind_ok]

/-- Translated Rust concatenation implements structural concatenation. -/
theorem concatenate_correct (left right : BalancedWord) :
    concatenate left right = .ok (appendWord left right) := by
  induction left with
  | Empty => rw [concatenate, copy_word_correct]; rfl
  | Pair head tail _ ih =>
    rw [concatenate, copy_word_correct, bind_ok, ih, bind_ok]
    rfl

/-- Pure model of the translated, score-based tie choice. -/
def selectResult (first second : CommonEmbedding) : CommonEmbedding :=
  if first.edges < second.edges then second else first

theorem choose_longer_correct (first second : CommonEmbedding) :
    choose_longer first second = .ok (selectResult first second) := by
  unfold choose_longer selectResult
  split <;> rfl

/-- Score consistency makes the Rust tie choice agree with the mathematical DP. -/
theorem selectResult_word (first second : CommonEmbedding)
    (hf : first.edges.val = (toDyck first.word).semilength)
    (hs : second.edges.val = (toDyck second.word).semilength) :
    toDyck (selectResult first second).word = longer (toDyck first.word) (toDyck second.word) := by
  unfold selectResult longer
  change toDyck (if first.edges.val < second.edges.val then second else first).word = _
  simp only [hf, hs]
  split <;> rfl

theorem selectResult_score (first second : CommonEmbedding)
    (hf : first.edges.val = (toDyck first.word).semilength)
    (hs : second.edges.val = (toDyck second.word).semilength) :
    (selectResult first second).edges.val = (toDyck (selectResult first second).word).semilength := by
  unfold selectResult
  split
  · exact hs
  · exact hf

/-- The modeled Rust checked addition succeeds whenever its mathematical sum fits. -/
theorem checked_add_success (first second : U32) (h : first.val + second.val < 2^32) :
    ∃ result, U32.checked_add first second = some result ∧ result.val = first.val + second.val := by
  have hs := U32.checked_add_bv_spec first second
  cases hc : U32.checked_add first second with
  | none =>
    rw [hc] at hs
    have hm : U32.max = 2^32-1 := by rw [U32.max_eq]; norm_num
    rw [hm] at hs
    omega
  | some result =>
    rw [hc] at hs
    exact ⟨result, rfl, hs.2.1⟩

/-- For accepted inputs, the actual translated Rust entry point terminates,
returns a witness equal to the certified recurrence, and reports its exact size. -/
theorem largest_common_embedding_refines (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : verified_ordered_core.CommonEmbedding,
      largest_common_embedding left right = .ok (some result) ∧
      toDyck result.word = paperCommon (toDyck left) (toDyck right) ∧
      result.edges.val = (toDyck result.word).semilength := by
  cases left with
  | Empty =>
    refine ⟨⟨.Empty, 0#u32⟩, ?_, ?_, ?_⟩
    · rw [largest_common_embedding]
    · simp [toDyck]
    · rfl
  | Pair lh lt =>
    cases right with
    | Empty =>
      refine ⟨⟨.Empty, 0#u32⟩, ?_, ?_, ?_⟩
      · rw [largest_common_embedding]
      · simp [toDyck]
      · rfl
    | Pair rh rt =>
      have hlSize := hl
      have hrSize := hr
      simp only [toDyck, DyckWord.semilength_add, DyckWord.semilength_nest] at hlSize hrSize
      obtain ⟨heads, hheadsRun, hheadsWord, hheadsScore⟩ := largest_common_embedding_refines lh rh
        (by omega) (by omega)
      obtain ⟨tails, htailsRun, htailsWord, htailsScore⟩ := largest_common_embedding_refines lt rt
        (by omega) (by omega)
      have hheadBound : heads.edges.val ≤ (toDyck lh).semilength := by
        rw [hheadsScore, hheadsWord]
        exact dyckEmbeds_semilength_le (paperCommon_sound _ _).1
      have htailBound : tails.edges.val ≤ (toDyck lt).semilength := by
        rw [htailsScore, htailsWord]
        exact dyckEmbeds_semilength_le (paperCommon_sound _ _).1
      obtain ⟨subtotal, hsum, hsubtotal⟩ := checked_add_success heads.edges tails.edges (by omega)
      obtain ⟨total, htotalRun, htotal⟩ := checked_add_success subtotal 1#u32 (by scalar_tac)
      obtain ⟨dropLeft, hdropLeftRun, hdropLeftWord, hdropLeftScore⟩ :=
        largest_common_embedding_refines (appendWord lh lt) (.Pair rh rt)
          (by simp only [toDyck_appendWord, DyckWord.semilength_add]; omega) hr
      obtain ⟨dropRight, hdropRightRun, hdropRightWord, hdropRightScore⟩ :=
        largest_common_embedding_refines (.Pair lh lt) (appendWord rh rt) hl
          (by simp only [toDyck_appendWord, DyckWord.semilength_add]; omega)
      let matched : verified_ordered_core.CommonEmbedding := ⟨.Pair heads.word tails.word, total⟩
      have hmatchedScore : matched.edges.val = (toDyck matched.word).semilength := by
        dsimp only [matched, toDyck]
        simp only [DyckWord.semilength_add, DyckWord.semilength_nest]
        have hone : (1#u32).val = 1 := rfl
        omega
      have hmatchedWord : toDyck matched.word =
          (paperCommon (toDyck lh) (toDyck rh)).nest + paperCommon (toDyck lt) (toDyck rt) := by
        simp only [matched, toDyck, hheadsWord, htailsWord]
      have hfirstScore := selectResult_score matched dropLeft hmatchedScore hdropLeftScore
      refine ⟨selectResult (selectResult matched dropLeft) dropRight, ?_, ?_,
        selectResult_score _ _ hfirstScore hdropRightScore⟩
      · rw [largest_common_embedding]
        simp only [hheadsRun, htailsRun, bind_ok, lift, hsum, htotalRun,
          concatenate_correct, hdropLeftRun, hdropRightRun, choose_longer_correct]
        rfl
      · calc
          toDyck (selectResult (selectResult matched dropLeft) dropRight).word =
              longer (toDyck (selectResult matched dropLeft).word) (toDyck dropRight.word) :=
            selectResult_word _ _ hfirstScore hdropRightScore
          _ = longer (longer (toDyck matched.word) (toDyck dropLeft.word)) (toDyck dropRight.word) := by
            rw [selectResult_word matched dropLeft hmatchedScore hdropLeftScore]
          _ = paperCommon (toDyck (.Pair lh lt)) (toDyck (.Pair rh rt)) := by
            rw [hmatchedWord, hdropLeftWord, hdropRightWord, toDyck_appendWord, toDyck_appendWord]
            exact (paperCommon_nest_add _ _ _ _).symm
termination_by (toDyck left).semilength + (toDyck right).semilength
decreasing_by
  all_goals subst_vars
  all_goals simp only [toDyck_appendWord, toDyck,
    DyckWord.semilength_add, DyckWord.semilength_nest]
  all_goals omega

/-- End-to-end functional correctness for the real translated Rust solver:
accepted inputs return an independently valid maximum tree and the exact score. -/
theorem largest_common_embedding_tree_correct (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : verified_ordered_core.CommonEmbedding,
      largest_common_embedding left right = .ok (some result) ∧
      IsMaximumCommon (decodeDyck (toDyck result.word))
        (decodeDyck (toDyck left)) (decodeDyck (toDyck right)) ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  obtain ⟨result, hrun, hword, hscore⟩ := largest_common_embedding_refines left right hl hr
  refine ⟨result, hrun, ?_, ?_⟩
  · apply longestCommonBalanced_decodes_maximum
    simpa only [encodeDyck_decodeDyck, hword] using paperCommon_correct (toDyck left) (toDyck right)
  · have hsize := encodeDyck_semilength (decodeDyck (toDyck result.word))
    rw [encodeDyck_decodeDyck] at hsize
    omega

/-- Every independently specified ordered-tree input is covered by the Rust
representation, with an explicit accepted-input bound and an optimal witness. -/
theorem largest_common_embedding_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : verified_ordered_core.CommonEmbedding,
      largest_common_embedding (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IsMaximumCommon (decodeDyck (toDyck result.word)) left right ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  have hlrep : (toDyck (fromDyck left.encodeDyck)).semilength < 2^32 := by
    simpa only [toDyck_fromDyck, encodeDyck_semilength] using hl
  have hrrep : (toDyck (fromDyck right.encodeDyck)).semilength < 2^32 := by
    simpa only [toDyck_fromDyck, encodeDyck_semilength] using hr
  simpa only [toDyck_fromDyck, decodeDyck_encodeDyck] using
    largest_common_embedding_tree_correct (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) hlrep hrrep

end SubtreeProofs.Rust.OrderedSolver

end
