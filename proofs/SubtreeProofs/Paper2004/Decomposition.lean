module

public import SubtreeProofs.Paper2004.BalancedSequence
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Finset.Union
import Mathlib.Tactic

/-!
# Lozano--Valiente decomposition families

These are the finite D, R and S families of Section 2, defined by their
balanced-word operations. They are DP states, not all edge contractions.
The printed leaf recurrence is kept separately from actual tree leaves.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004
namespace BalancedDecomposition

/-- Removing the first pair decreases semilength by exactly one. -/
theorem contracted_semilength {word : DyckWord} (h : word ≠ 0) :
    (word.insidePart + word.outsidePart).semilength + 1 = word.semilength := by
  simpa only [DyckWord.semilength_add] using
    DyckWord.semilength_insidePart_add_semilength_outsidePart_add_one h

/-- The least decomposition family of Definition 4, in executable finite form. -/
def states (word : DyckWord) : Finset DyckWord :=
  if _h : word = 0 then {0} else
    insert word (states word.insidePart ∪ states word.outsidePart ∪
      states (word.insidePart + word.outsidePart))
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- R repeatedly deletes the first matched pair. -/
def frontContractions (word : DyckWord) : Finset DyckWord :=
  if _h : word = 0 then {0} else
    insert word (frontContractions (word.insidePart + word.outsidePart))
termination_by word.semilength
decreasing_by
  have hc := contracted_semilength (word := word) (by assumption)
  omega

/-- S collects R of successive heads while deleting first pairs. -/
def headContractions (word : DyckWord) : Finset DyckWord :=
  if _h : word = 0 then {0} else
    frontContractions word.insidePart ∪ headContractions (word.insidePart + word.outsidePart)
termination_by word.semilength
decreasing_by
  have hc := contracted_semilength (word := word) (by assumption)
  omega


@[simp] theorem states_zero : states 0 = {0} := by rw [states]; simp
@[simp] theorem frontContractions_zero : frontContractions 0 = {0} := by
  rw [frontContractions]; simp
@[simp] theorem headContractions_zero : headContractions 0 = {0} := by
  rw [headContractions]; simp

/-- Every nonempty first-return decomposition has a nonempty first pair. -/
theorem nest_add_ne_zero (head tail : DyckWord) : head.nest + tail ≠ 0 := by
  intro h
  have hc := congrArg DyckWord.semilength h
  simp only [DyckWord.semilength_add, DyckWord.semilength_nest,
    DyckWord.semilength_zero] at hc
  omega

@[simp] theorem states_nest_add (head tail : DyckWord) :
    states (head.nest + tail) =
      insert (head.nest + tail) (states head ∪ states tail ∪ states (head + tail)) := by
  rw [states]
  simp only [nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

@[simp] theorem frontContractions_nest_add (head tail : DyckWord) :
    frontContractions (head.nest + tail) =
      insert (head.nest + tail) (frontContractions (head + tail)) := by
  rw [frontContractions]
  simp only [nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

@[simp] theorem headContractions_nest_add (head tail : DyckWord) :
    headContractions (head.nest + tail) =
      frontContractions head ∪ headContractions (head + tail) := by
  rw [headContractions]
  simp only [nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

/-- Lemma 1: wordSuffix decomposition states remain available after a wordPrefix. -/
theorem states_suffix (wordPrefix wordSuffix : DyckWord) :
    states wordSuffix ⊆ states (wordPrefix + wordSuffix) := by
  by_cases hp : wordPrefix = 0
  · simp [hp]
  · have ih := states_suffix wordPrefix.outsidePart wordSuffix
    rw [← DyckWord.nest_insidePart_add_outsidePart hp, add_assoc, states_nest_add]
    intro state hs
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_right _ (ih hs)))
termination_by wordPrefix.semilength
decreasing_by exact DyckWord.semilength_outsidePart_lt (by assumption)


/-- Lemma 2: prefix states survive either in the concatenation or in R. -/
theorem states_prefix (first second : DyckWord) :
    states first ⊆ states (first + second) ∪ frontContractions first := by
  by_cases hf : first = 0
  · simp [hf]
  · have ih := states_prefix (first.insidePart + first.outsidePart) second
    have hfirst := DyckWord.nest_insidePart_add_outsidePart hf
    have hcat : first + second = first.insidePart.nest + (first.outsidePart + second) := by
      calc
        first + second = (first.insidePart.nest + first.outsidePart) + second :=
          congrArg (fun word => word + second) hfirst.symm
        _ = _ := add_assoc _ _ _
    have hdecomp : states first = insert first
        (states first.insidePart ∪ states first.outsidePart ∪
          states (first.insidePart + first.outsidePart)) := by
      calc
        states first = states (first.insidePart.nest + first.outsidePart) := congrArg states hfirst.symm
        _ = _ := by rw [states_nest_add, hfirst]
    have hfront : frontContractions first = insert first
        (frontContractions (first.insidePart + first.outsidePart)) := by
      calc
        frontContractions first = frontContractions (first.insidePart.nest + first.outsidePart) :=
          congrArg frontContractions hfirst.symm
        _ = _ := by rw [frontContractions_nest_add, hfirst]
    intro state hstate
    rw [hdecomp] at hstate
    rw [hcat, states_nest_add, hfront]
    rcases Finset.mem_insert.mp hstate with heq | hstate
    · simp [heq]
    · rcases Finset.mem_union.mp hstate with hleft | hcontracted
      · rcases Finset.mem_union.mp hleft with hhead | htail
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
            (Finset.mem_union_left _ (Finset.mem_union_left _ hhead)))
        · have hmerged := states_suffix first.insidePart first.outsidePart htail
          rcases Finset.mem_union.mp (ih hmerged) with hconcat | hr
          · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
              (Finset.mem_union_right _ (by simpa only [add_assoc] using hconcat)))
          · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hr)
      · rcases Finset.mem_union.mp (ih hcontracted) with hconcat | hr
        · exact Finset.mem_union_left _ (Finset.mem_insert_of_mem
            (Finset.mem_union_right _ (by simpa only [add_assoc] using hconcat)))
        · exact Finset.mem_union_right _ (Finset.mem_insert_of_mem hr)
termination_by first.semilength
decreasing_by have hc := contracted_semilength (word := first) (by assumption); omega

/-- Lemma 3: one decomposition step is covered by the contracted word and R(head). -/
theorem states_nest_subset (head tail : DyckWord) :
    states (head.nest + tail) ⊆
      insert (head.nest + tail) (states (head + tail) ∪ frontContractions head) := by
  rw [states_nest_add]
  intro state hstate
  rcases Finset.mem_insert.mp hstate with rfl | hstate
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    rcases Finset.mem_union.mp hstate with hleft | hcontracted
    · rcases Finset.mem_union.mp hleft with hhead | htail
      · exact states_prefix head tail hhead
      · exact Finset.mem_union_left _ (states_suffix head tail htail)
    · exact Finset.mem_union_left _ hcontracted


/-- The first-return form of R without changing occurrences inside the word. -/
theorem frontContractions_of_ne_zero (word : DyckWord) (h : word ≠ 0) :
    frontContractions word = insert word
      (frontContractions (word.insidePart + word.outsidePart)) := by
  rw [frontContractions]
  simp only [h, ↓reduceDIte]

/-- The first-return form of S. -/
theorem headContractions_of_ne_zero (word : DyckWord) (h : word ≠ 0) :
    headContractions word = frontContractions word.insidePart ∪
      headContractions (word.insidePart + word.outsidePart) := by
  rw [headContractions]
  simp only [h, ↓reduceDIte]

/-- R includes its input. -/
theorem mem_frontContractions_self (word : DyckWord) : word ∈ frontContractions word := by
  by_cases h : word = 0
  · simp [h]
  · rw [frontContractions_of_ne_zero word h]
    exact Finset.mem_insert_self _ _

/-- R is closed under continuing first-pair contractions. -/
theorem frontContractions_subset {small large : DyckWord}
    (hmem : small ∈ frontContractions large) :
    frontContractions small ⊆ frontContractions large := by
  by_cases hl : large = 0
  · simp only [hl, frontContractions_zero, Finset.mem_singleton] at hmem
    subst small
    simp [hl]
  · rw [frontContractions_of_ne_zero large hl] at hmem ⊢
    rcases Finset.mem_insert.mp hmem with rfl | hm
    · rw [frontContractions_of_ne_zero _ hl]
    · exact (frontContractions_subset hm).trans (Finset.subset_insert _ _)
termination_by large.semilength
decreasing_by have hc := contracted_semilength (word := large) (by assumption); omega

/-- S can only shrink along the front-contraction chain. -/
theorem headContractions_subset {small large : DyckWord}
    (hmem : small ∈ frontContractions large) :
    headContractions small ⊆ headContractions large := by
  by_cases hl : large = 0
  · simp only [hl, frontContractions_zero, Finset.mem_singleton] at hmem
    subst small
    simp [hl]
  · rw [frontContractions_of_ne_zero large hl] at hmem
    rcases Finset.mem_insert.mp hmem with rfl | hm
    · exact Finset.Subset.refl _
    · rw [headContractions_of_ne_zero large hl]
      exact (headContractions_subset hm).trans (Finset.subset_union_right)
termination_by large.semilength
decreasing_by have hc := contracted_semilength (word := large) (by assumption); omega

/-- R of any nonempty front state's head belongs to the original S. -/
theorem head_frontContractions_subset {small large : DyckWord}
    (hmem : small ∈ frontContractions large) (hs : small ≠ 0) :
    frontContractions small.insidePart ⊆ headContractions large := by
  apply Finset.Subset.trans _ (headContractions_subset hmem)
  rw [headContractions_of_ne_zero small hs]
  exact Finset.subset_union_left

/-- Lemma 4: D of any front state followed by a suffix has three finite sources. -/
theorem states_front_append {word state : DyckWord} (second : DyckWord)
    (hmem : state ∈ frontContractions word) :
    states (state + second) ⊆ states second ∪
      (frontContractions word).image (fun part => part + second) ∪ headContractions word := by
  by_cases hs : state = 0
  · simp only [hs, zero_add]
    exact (Finset.subset_union_left).trans Finset.subset_union_left
  · have hstate := DyckWord.nest_insidePart_add_outsidePart hs
    have hcat : state + second = state.insidePart.nest + (state.outsidePart + second) := by
      calc
        state + second = (state.insidePart.nest + state.outsidePart) + second :=
          congrArg (fun part => part + second) hstate.symm
        _ = _ := add_assoc _ _ _
    have hnext : state.insidePart + state.outsidePart ∈ frontContractions word := by
      apply frontContractions_subset hmem
      rw [frontContractions_of_ne_zero state hs]
      exact Finset.mem_insert_of_mem (mem_frontContractions_self _)
    have ih := states_front_append second hnext
    intro part hp
    rw [hcat] at hp
    have hsplit := states_nest_subset state.insidePart (state.outsidePart + second) hp
    rcases Finset.mem_insert.mp hsplit with heq | hrest
    · rw [← hcat] at heq
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨state, hmem, heq.symm⟩))
    · rcases Finset.mem_union.mp hrest with hcontracted | hhead
      · apply ih
        simpa only [add_assoc] using hcontracted
      · exact Finset.mem_union_right _ (head_frontContractions_subset hmem hs hhead)
termination_by state.semilength
decreasing_by have hc := contracted_semilength (word := state) (by assumption); omega

/-- Empty is on every R chain. -/
theorem zero_mem_frontContractions (word : DyckWord) : 0 ∈ frontContractions word := by
  by_cases h : word = 0
  · simp [h]
  · rw [frontContractions_of_ne_zero word h]
    exact Finset.mem_insert_of_mem (zero_mem_frontContractions _)
termination_by word.semilength
decreasing_by have hc := contracted_semilength (word := word) (by assumption); omega

/-- Corollary 1: D is covered by R and S. -/
theorem states_subset_front_union_head (word : DyckWord) :
    states word ⊆ frontContractions word ∪ headContractions word := by
  have h := states_front_append 0 (mem_frontContractions_self word)
  simp only [add_zero, states_zero, Finset.image_id'] at h
  intro state hs
  rcases Finset.mem_union.mp (h hs) with hleft | hright
  · rcases Finset.mem_union.mp hleft with hz | hr
    · have heq := Finset.mem_singleton.mp hz
      subst state
      exact Finset.mem_union_left _ (zero_mem_frontContractions word)
    · exact Finset.mem_union_left _ hr
  · exact Finset.mem_union_right _ hright

/-- Lemma 5: S of a concatenation is covered by S of its two inputs. -/
theorem headContractions_append (first second : DyckWord) :
    headContractions (first + second) ⊆ headContractions first ∪ headContractions second := by
  by_cases hf : first = 0
  · simp only [hf, zero_add]
    exact Finset.subset_union_right
  · have ih := headContractions_append (first.insidePart + first.outsidePart) second
    have hfirst := DyckWord.nest_insidePart_add_outsidePart hf
    have hcat : first + second = first.insidePart.nest + (first.outsidePart + second) := by
      calc
        first + second = (first.insidePart.nest + first.outsidePart) + second :=
          congrArg (fun part => part + second) hfirst.symm
        _ = _ := add_assoc _ _ _
    rw [hcat, headContractions_nest_add, headContractions_of_ne_zero first hf]
    intro state hs
    rcases Finset.mem_union.mp hs with hhead | htail
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ hhead)
    · have htail' : state ∈ headContractions ((first.insidePart + first.outsidePart) + second) := by
        simpa only [add_assoc] using htail
      rcases Finset.mem_union.mp (ih htail') with hleft | hright
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hleft)
      · exact Finset.mem_union_right _ hright
termination_by first.semilength
decreasing_by have hc := contracted_semilength (word := first) (by assumption); omega


/-- A first-pair contraction stays in D. -/
theorem states_contract_subset {word : DyckWord} (h : word ≠ 0) :
    states (word.insidePart + word.outsidePart) ⊆ states word := by
  have hw := DyckWord.nest_insidePart_add_outsidePart h
  calc
    states (word.insidePart + word.outsidePart) ⊆
        states (word.insidePart.nest + word.outsidePart) := by
      rw [states_nest_add]
      exact Finset.Subset.trans Finset.subset_union_right (Finset.subset_insert _ _)
    _ = states word := congrArg states hw

/-- R is contained in the decomposition. -/
theorem frontContractions_subset_states (word : DyckWord) :
    frontContractions word ⊆ states word := by
  by_cases hw : word = 0
  · simp [hw]
  · rw [frontContractions_of_ne_zero word hw]
    intro state hs
    rcases Finset.mem_insert.mp hs with rfl | hstate
    · rw [states]
      simp only [hw, ↓reduceDIte]
      exact Finset.mem_insert_self _ _
    · exact states_contract_subset hw (frontContractions_subset_states _ hstate)
termination_by word.semilength
decreasing_by have hc := contracted_semilength (word := word) (by assumption); omega

/-- S is contained in the decomposition. -/
theorem headContractions_subset_states (word : DyckWord) :
    headContractions word ⊆ states word := by
  by_cases hw : word = 0
  · simp [hw]
  · rw [headContractions_of_ne_zero word hw]
    intro state hs
    rcases Finset.mem_union.mp hs with hh | ht
    · have hhead := frontContractions_subset_states word.insidePart hh
      have hform := DyckWord.nest_insidePart_add_outsidePart hw
      have hm : state ∈ states (word.insidePart.nest + word.outsidePart) := by
        rw [states_nest_add]
        exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hhead))
      simpa only [hform] using hm
    · exact states_contract_subset hw (headContractions_subset_states _ ht)
termination_by word.semilength
decreasing_by have hc := contracted_semilength (word := word) (by assumption); omega

/-- The two families in Corollary 1 exactly cover D. -/
theorem states_eq_front_union_head (word : DyckWord) :
    states word = frontContractions word ∪ headContractions word := by
  apply Finset.Subset.antisymm (states_subset_front_union_head word)
  exact Finset.union_subset (frontContractions_subset_states word) (headContractions_subset_states word)


/-- Every decomposition contains the original word. -/
theorem mem_states_self (word : DyckWord) : word ∈ states word :=
  frontContractions_subset_states word (mem_frontContractions_self word)

/-- Continuing decomposition from any state cannot leave the original D family. -/
theorem states_trans {small large : DyckWord} (hmem : small ∈ states large) :
    states small ⊆ states large := by
  by_cases hz : large = 0
  · have hsmall : small = 0 := by simpa only [hz, states_zero, Finset.mem_singleton] using hmem
    subst small
    simp only [hz, states_zero, Finset.Subset.refl]
  · have hform : states large = insert large
        (states large.insidePart ∪ states large.outsidePart ∪ states (large.insidePart + large.outsidePart)) := by
      rw [states]
      simp only [hz, ↓reduceDIte]
    rw [hform] at hmem
    rcases Finset.mem_insert.mp hmem with rfl | hs
    · exact Finset.Subset.refl _
    · rcases Finset.mem_union.mp hs with hleft | hc
      · rcases Finset.mem_union.mp hleft with hh | ht
        · apply Finset.Subset.trans (states_trans hh)
          rw [hform]
          intro state hs
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_left _ hs))
        · apply Finset.Subset.trans (states_trans ht)
          rw [hform]
          intro state hs
          exact Finset.mem_insert_of_mem (Finset.mem_union_left _ (Finset.mem_union_right _ hs))
      · apply Finset.Subset.trans (states_trans hc)
        rw [hform]
        intro state hs
        exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hs)
termination_by large.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := large) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Definition 4's three closure rules hold for the executable state family. -/
theorem states_closed {word state : DyckWord} (hmem : state ∈ states word) (hs : state ≠ 0) :
    state.insidePart ∈ states word ∧ state.outsidePart ∈ states word ∧
      state.insidePart + state.outsidePart ∈ states word := by
  have ht := states_trans hmem
  have hhead : state.insidePart ∈ states state := by
    rw [states]
    simp only [hs, ↓reduceDIte]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_left _ (mem_states_self _)))
  have htail : state.outsidePart ∈ states state := by
    rw [states]
    simp only [hs, ↓reduceDIte]
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _
      (Finset.mem_union_right _ (mem_states_self _)))
  have hcontract : state.insidePart + state.outsidePart ∈ states state :=
    states_contract_subset hs (mem_states_self _)
  exact ⟨ht hhead, ht htail, ht hcontract⟩

/-- Definition 4's leastness: any predicate containing the input and closed
under the three operations contains every enumerated state. -/
theorem states_least (word : DyckWord) (P : DyckWord → Prop) (hroot : P word)
    (hclosed : ∀ state, P state → state ≠ 0 →
      P state.insidePart ∧ P state.outsidePart ∧ P (state.insidePart + state.outsidePart)) :
    ∀ state ∈ states word, P state := by
  intro state hmem
  rw [states] at hmem
  split at hmem
  · rename_i hz
    have hstate := Finset.mem_singleton.mp hmem
    simpa only [hz, hstate] using hroot
  · rename_i hn
    obtain ⟨hh, ht, hc⟩ := hclosed word hroot hn
    rcases Finset.mem_insert.mp hmem with rfl | hs
    · exact hroot
    · rcases Finset.mem_union.mp hs with hleft | hcontract
      · rcases Finset.mem_union.mp hleft with hhead | htail
        · exact states_least word.insidePart P hh hclosed state hhead
        · exact states_least word.outsidePart P ht hclosed state htail
      · exact states_least (word.insidePart + word.outsidePart) P hc hclosed state hcontract
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- The printed ell recurrence, deliberately not named leafCount. -/
def printedLeafMeasure (word : DyckWord) : Nat :=
  if _h : word = 0 then 1 else
    printedLeafMeasure word.insidePart + printedLeafMeasure word.outsidePart
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- The printed recurrence counts edges plus one rather than actual leaves. -/
theorem printedLeafMeasure_eq (word : DyckWord) :
    printedLeafMeasure word = word.semilength + 1 := by
  rw [printedLeafMeasure]
  split
  · rename_i h
    simp [h]
  · rename_i h
    rw [printedLeafMeasure_eq word.insidePart, printedLeafMeasure_eq word.outsidePart]
    have hc := contracted_semilength h
    simp only [DyckWord.semilength_add] at hc
    omega
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- One edge suffices to distinguish the printed measure from tree leaves. -/
theorem printedLeafMeasure_oneEdge :
    printedLeafMeasure (OrderedTree.encodeDyck OrderedTree.oneEdge) = 2 ∧
      OrderedTree.leafCount OrderedTree.oneEdge = 1 := by
  simp [printedLeafMeasure_eq, OrderedTree.encodeDyck_semilength]


/-- Paper depth counts the singleton root as one. -/
def sequenceDepth (word : DyckWord) : Nat :=
  if _h : word = 0 then 1 else
    max (sequenceDepth word.insidePart + 1) (sequenceDepth word.outsidePart)
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

@[simp] theorem sequenceDepth_zero : sequenceDepth 0 = 1 := by rw [sequenceDepth]; simp

@[simp] theorem sequenceDepth_nest_add (head tail : DyckWord) :
    sequenceDepth (head.nest + tail) = max (sequenceDepth head + 1) (sequenceDepth tail) := by
  rw [sequenceDepth]
  simp only [nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

theorem sequenceDepth_pos (word : DyckWord) : 0 < sequenceDepth word := by
  rw [sequenceDepth]
  split <;> omega

/-- Nonempty words describe a root and at least one child. -/
theorem sequenceDepth_nonempty {word : DyckWord} (h : word ≠ 0) :
    2 ≤ sequenceDepth word := by
  rw [sequenceDepth]
  simp only [h, ↓reduceDIte]
  have hp := sequenceDepth_pos word.insidePart
  omega


/-- Actual leaf count on balanced words: an empty tail contributes no extra root. -/
def trueLeafMeasure (word : DyckWord) : Nat :=
  if _h : word = 0 then 1 else
    trueLeafMeasure word.insidePart +
      if word.outsidePart = 0 then 0 else trueLeafMeasure word.outsidePart
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

@[simp] theorem trueLeafMeasure_zero : trueLeafMeasure 0 = 1 := by rw [trueLeafMeasure]; simp

@[simp] theorem trueLeafMeasure_nest_add (head tail : DyckWord) :
    trueLeafMeasure (head.nest + tail) =
      trueLeafMeasure head + if tail = 0 then 0 else trueLeafMeasure tail := by
  rw [trueLeafMeasure]
  simp only [nest_add_ne_zero, ↓reduceDIte,
    DyckWord.insidePart_add DyckWord.nest_ne_zero,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,
    DyckWord.insidePart_nest, DyckWord.outsidePart_nest, zero_add]

/-- Every represented tree has at least one actual leaf. -/
theorem trueLeafMeasure_pos (word : DyckWord) : 0 < trueLeafMeasure word := by
  rw [trueLeafMeasure]
  split
  · omega
  · have hh := trueLeafMeasure_pos word.insidePart
    omega
termination_by word.semilength
decreasing_by
  have hc := contracted_semilength (word := word) (by assumption)
  simp only [DyckWord.semilength_add] at hc
  omega

/-- Every R state has at most the input's semilength. -/
theorem frontContractions_semilength {word state : DyckWord}
    (hmem : state ∈ frontContractions word) : state.semilength ≤ word.semilength := by
  rw [frontContractions] at hmem
  split at hmem
  · rename_i h
    simp only [Finset.mem_singleton] at hmem
    subst state
    simp [h]
  · rename_i h
    rcases Finset.mem_insert.mp hmem with rfl | hm
    · exact Nat.le_refl _
    · have hi := frontContractions_semilength hm
      have hc := contracted_semilength h
      omega
termination_by word.semilength
decreasing_by
  have hc := contracted_semilength (word := word) (by assumption)
  omega

/-- Fact 2: R contains exactly one state at each remaining edge count. -/
theorem frontContractions_card (word : DyckWord) :
    (frontContractions word).card = word.semilength + 1 := by
  rw [frontContractions]
  split
  · rename_i h
    simp [h]
  · rename_i h
    have hnot : word ∉ frontContractions (word.insidePart + word.outsidePart) := by
      intro hm
      have hi := frontContractions_semilength hm
      have hc := contracted_semilength h
      omega
    rw [Finset.card_insert_of_notMem hnot, frontContractions_card]
    have hc := contracted_semilength h
    omega
termination_by word.semilength
decreasing_by
  have hc := contracted_semilength (word := word) (by assumption)
  omega

/-- Lemma 6: the actual finite S family has the paper's depth-sensitive bound. -/
theorem headContractions_card_depth (word : DyckWord) :
    (headContractions word).card ≤ word.semilength * sequenceDepth word + 1 := by
  by_cases hw : word = 0
  · simp [hw]
  · have ih := headContractions_card_depth word.insidePart
    have it := headContractions_card_depth word.outsidePart
    have hs : (headContractions (word.insidePart + word.outsidePart)).card ≤
        (headContractions word.insidePart).card + (headContractions word.outsidePart).card :=
      (Finset.card_le_card (headContractions_append _ _)).trans (Finset.card_union_le _ _)
    have hu := Finset.card_union_le (frontContractions word.insidePart)
      (headContractions (word.insidePart + word.outsidePart))
    rw [← headContractions_of_ne_zero word hw, frontContractions_card] at hu
    have hc := contracted_semilength hw
    simp only [DyckWord.semilength_add] at hc
    have hd : sequenceDepth word =
        max (sequenceDepth word.insidePart + 1) (sequenceDepth word.outsidePart) := by
      rw [sequenceDepth]
      simp only [hw, ↓reduceDIte]
    have hd1 : sequenceDepth word.insidePart + 1 ≤ sequenceDepth word := by rw [hd]; exact le_max_left _ _
    have hd2 : sequenceDepth word.outsidePart ≤ sequenceDepth word := by rw [hd]; exact le_max_right _ _
    have hd3 := sequenceDepth_nonempty hw
    have hmul1 := Nat.mul_le_mul_left word.insidePart.semilength hd1
    have hmul2 := Nat.mul_le_mul_left word.outsidePart.semilength hd2
    nlinarith
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- The depth specialization of Theorem 1 follows from the two finite families. -/
theorem states_card_depth (word : DyckWord) :
    (states word).card ≤ word.semilength * (sequenceDepth word + 1) + 1 := by
  have hsub := Finset.card_le_card (states_subset_front_union_head word)
  have hu := Finset.card_union_le (frontContractions word) (headContractions word)
  have hz : 0 ∈ frontContractions word ∩ headContractions word := by
    refine Finset.mem_inter.mpr ⟨zero_mem_frontContractions word, ?_⟩
    by_cases hw : word = 0
    · simp [hw]
    · rw [headContractions_of_ne_zero word hw]
      exact Finset.mem_union_left _ (zero_mem_frontContractions _)
  have hi : 1 ≤ (frontContractions word ∩ headContractions word).card :=
    Finset.one_le_card.mpr ⟨0, hz⟩
  have heq := Finset.card_union_add_card_inter (frontContractions word) (headContractions word)
  have hr := frontContractions_card word
  have hs := headContractions_card_depth word
  nlinarith

/-- A state decomposition charging the first child's family only once. -/
theorem states_nest_add_charge (head tail : DyckWord) :
    states (head.nest + tail) ⊆ insert (head.nest + tail)
      (states head ∪ states tail ∪ (frontContractions head).image (fun part => part + tail)) := by
  intro state hs
  rcases Finset.mem_insert.mp (states_nest_subset head tail hs) with heq | hrest
  · exact Finset.mem_insert.mpr (Or.inl heq)
  · apply Finset.mem_insert_of_mem
    rcases Finset.mem_union.mp hrest with hconcat | hr
    · have hdecomp := states_front_append tail (mem_frontContractions_self head) hconcat
      rcases Finset.mem_union.mp hdecomp with hleft | hright
      · rcases Finset.mem_union.mp hleft with ht | himage
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ ht)
        · exact Finset.mem_union_right _ himage
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (headContractions_subset_states head hright))
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (frontContractions_subset_states head hr))

/-- Corrected actual-leaf estimates. Unlike the printed ell proof, this argument
handles the empty tail separately and shares the R/S charge through D. -/
theorem card_true_leaf_bounds (word : DyckWord) :
    (states word).card ≤ (word.semilength + 1) * trueLeafMeasure word ∧
      (headContractions word).card ≤ word.semilength * trueLeafMeasure word + 1 := by
  by_cases hw : word = 0
  · simp [hw]
  · have ih := card_true_leaf_bounds word.insidePart
    have it := card_true_leaf_bounds word.outsidePart
    have hword := DyckWord.nest_insidePart_add_outsidePart hw
    have hn := contracted_semilength hw
    simp only [DyckWord.semilength_add] at hn
    have hpos := trueLeafMeasure_pos word.insidePart
    have hl : trueLeafMeasure word = trueLeafMeasure word.insidePart +
        if word.outsidePart = 0 then 0 else trueLeafMeasure word.outsidePart := by
      calc
        trueLeafMeasure word = trueLeafMeasure (word.insidePart.nest + word.outsidePart) :=
          congrArg trueLeafMeasure hword.symm
        _ = _ := trueLeafMeasure_nest_add _ _
    by_cases ht : word.outsidePart = 0
    · have hd : states word = insert word (states word.insidePart) := by
        calc
          states word = states (word.insidePart.nest + word.outsidePart) := congrArg states hword.symm
          _ = insert (word.insidePart.nest + word.outsidePart)
              (states word.insidePart ∪ states word.outsidePart ∪
                states (word.insidePart + word.outsidePart)) := states_nest_add _ _
          _ = _ := by
            have hz : 0 ∈ states word.insidePart :=
              frontContractions_subset_states _ (zero_mem_frontContractions _)
            have hnest : word.insidePart.nest = word := by simpa only [ht, add_zero] using hword
            simp only [ht, add_zero, states_zero, hnest]
            ext state
            simp only [Finset.mem_insert, Finset.mem_union, Finset.mem_singleton]
            aesop
      have hs : headContractions word = states word.insidePart := by
        rw [headContractions_of_ne_zero word hw, ht, add_zero, ← states_eq_front_union_head]
      have hc := Finset.card_insert_le word (states word.insidePart)
      rw [← hd] at hc
      simp only [ht, DyckWord.semilength_zero, add_zero, ↓reduceIte] at hn hl
      rw [hs]
      constructor <;> nlinarith [ih.1]
    · have hpos2 := trueLeafMeasure_pos word.outsidePart
      simp only [ht, ↓reduceIte] at hl
      have hs : (headContractions word).card ≤ (states word.insidePart).card +
          (headContractions word.outsidePart).card := by
        rw [headContractions_of_ne_zero word hw]
        have hsub : frontContractions word.insidePart ∪ headContractions (word.insidePart + word.outsidePart) ⊆
            states word.insidePart ∪ headContractions word.outsidePart := by
          intro state hs
          rcases Finset.mem_union.mp hs with hr | hc
          · exact Finset.mem_union_left _ (frontContractions_subset_states _ hr)
          · rcases Finset.mem_union.mp (headContractions_append _ _ hc) with hh | ht
            · exact Finset.mem_union_left _ (headContractions_subset_states _ hh)
            · exact Finset.mem_union_right _ ht
        exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have hd : (states word).card ≤ (states word.insidePart).card +
          (states word.outsidePart).card + word.insidePart.semilength + 2 := by
        have hsub := states_nest_add_charge word.insidePart word.outsidePart
        rw [hword] at hsub
        have hc := Finset.card_le_card hsub
        have hi := Finset.card_insert_le word
          (states word.insidePart ∪ states word.outsidePart ∪
            (frontContractions word.insidePart).image (fun part => part + word.outsidePart))
        have hu := Finset.card_union_le (states word.insidePart ∪ states word.outsidePart)
          ((frontContractions word.insidePart).image (fun part => part + word.outsidePart))
        have hu2 := Finset.card_union_le (states word.insidePart) (states word.outsidePart)
        have him := Finset.card_image_le (s := frontContractions word.insidePart)
          (f := fun part => part + word.outsidePart)
        rw [frontContractions_card] at him
        omega
      constructor
      · nlinarith [ih.1, it.1,
          Nat.mul_le_mul_left (word.outsidePart.semilength + 1) hpos,
          Nat.mul_le_mul_left (word.insidePart.semilength + 1) hpos2]
      · nlinarith [ih.1, it.2]
termination_by word.semilength
decreasing_by
  all_goals have hc := contracted_semilength (word := word) (by assumption)
  all_goals simp only [DyckWord.semilength_add] at *
  all_goals omega

/-- Theorem 1's leaf specialization, using the corrected actual-leaf recurrence. -/
theorem states_card_leaf (word : DyckWord) :
    (states word).card ≤ word.semilength * (trueLeafMeasure word + 1) + 1 := by
  have hsub := Finset.card_le_card (states_subset_front_union_head word)
  have hs := (card_true_leaf_bounds word).2
  have hr := frontContractions_card word
  have heq := Finset.card_union_add_card_inter (frontContractions word) (headContractions word)
  have hz : 0 ∈ frontContractions word ∩ headContractions word := by
    refine Finset.mem_inter.mpr ⟨zero_mem_frontContractions word, ?_⟩
    by_cases hw : word = 0
    · simp [hw]
    · rw [headContractions_of_ne_zero word hw]
      exact Finset.mem_union_left _ (zero_mem_frontContractions _)
  have hi : 1 ≤ (frontContractions word ∩ headContractions word).card := Finset.one_le_card.mpr ⟨0, hz⟩
  nlinarith

/-- Corrected Theorem 1, with the genuine leaf measure and vertex depth. -/
theorem states_card_min_depth_leaf (word : DyckWord) :
    (states word).card ≤
      word.semilength * (min (sequenceDepth word) (trueLeafMeasure word) + 1) + 1 := by
  rcases le_total (sequenceDepth word) (trueLeafMeasure word) with hd | hl
  · rw [min_eq_left hd]
    exact states_card_depth word
  · rw [min_eq_right hl]
    exact states_card_leaf word

end BalancedDecomposition
end SubtreeProofs.Paper2004

end
