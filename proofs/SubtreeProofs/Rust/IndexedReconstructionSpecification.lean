module

public import SubtreeProofs.Rust.IndexedWordRepresentation
import Mathlib.Tactic

/-! # Independent indexed reconstruction outcomes and the forced-deletion case -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedOrderedSolver

open OrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- Reconstruction returns a genuine original-index contraction with exactly
the requested shape, or an independent proof that no such shape is contained. -/
def ReconstructionOutcome (pattern : BalancedWord) (input : indexed.IndexedWord) (output : Option indexed.IndexedWord) : Prop :=
  match output with
  | some word => Retains (model word) (model input) ∧ erase (model word) = toDyck pattern
  | none => ¬ DyckEmbeds (toDyck pattern) (erase (model input))

/-- If keeping the source first pair cannot realize either required part,
every independent embedding of the whole pattern must delete that pair. -/
theorem must_drop_first (patternHead patternTail sourceHead sourceTail : DyckWord)
    (h : DyckEmbeds (patternHead.nest+patternTail) (sourceHead.nest+sourceTail))
    (hrejected : ¬ DyckEmbeds patternHead sourceHead ∨ ¬ DyckEmbeds patternTail sourceTail) :
    DyckEmbeds (patternHead.nest+patternTail) (sourceHead+sourceTail) := by
  rcases dyckEmbeds_first_pair h with hdropped | ⟨inside,outside,hshape,hinside,houtside⟩
  · exact hdropped
  · have hh := congrArg DyckWord.insidePart hshape
    have ht := congrArg DyckWord.outsidePart hshape
    simp only [DyckWord.insidePart_add DyckWord.nest_ne_zero,DyckWord.insidePart_nest] at hh
    simp only [DyckWord.outsidePart_add DyckWord.nest_ne_zero,DyckWord.outsidePart_nest,zero_add] at ht
    rw [← hh] at hinside
    rw [← ht] at houtside
    rcases hrejected with hn | hn
    · exact False.elim (hn hinside)
    · exact False.elim (hn houtside)

/-- The independent witness/nonexistence result on the contracted first pair
transports to the original indexed input when the keep case is impossible. -/
theorem fallback_outcome (ph pt : BalancedWord) (index : U32) (head tail : indexed.IndexedWord) (output : Option indexed.IndexedWord)
    (hrejected : ¬ DyckEmbeds (toDyck ph) (erase (model head)) ∨ ¬ DyckEmbeds (toDyck pt) (erase (model tail)))
    (h : ReconstructionOutcome (.Pair ph pt) (appendWord head tail) output) :
    ReconstructionOutcome (.Pair ph pt) (.Pair index head tail) output := by
  cases output with
  | some word =>
    obtain ⟨hretains,hshape⟩ := h
    have hroot : Retains (model (appendWord head tail)) (model (.Pair index head tail)) := by
      rw [model_appendWord]
      exact Relation.ReflTransGen.single (Step.root index.val (model head) (model tail))
    exact ⟨hretains.trans hroot,hshape⟩
  | none =>
    change ¬ DyckEmbeds (toDyck (.Pair ph pt)) (erase (model (.Pair index head tail)))
    intro he
    apply h
    rw [model_appendWord,erase_append]
    apply must_drop_first (toDyck ph) (toDyck pt) (erase (model head)) (erase (model tail)) _ hrejected
    simpa only [toDyck,model,erase] using he

end SubtreeProofs.Rust.IndexedOrderedSolver

end
