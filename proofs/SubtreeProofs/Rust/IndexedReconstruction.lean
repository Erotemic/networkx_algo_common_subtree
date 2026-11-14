module

public import SubtreeProofs.Rust.IndexedReconstructionSpecification
import Mathlib.Tactic

/-! # Total source correctness of original-index contraction reconstruction -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedOrderedSolver

open OrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- Every actual reconstruction call terminates and either returns a genuine
indexed contraction of precisely the requested shape, or rejects a shape that
is independently not obtainable by contractions. No feasibility premise is
needed for this total helper contract. -/
theorem reconstruct_embedding_refines (pattern : BalancedWord) (input : indexed.IndexedWord) :
    ∃ output, indexed.reconstruct_embedding pattern input = .ok output ∧ ReconstructionOutcome pattern input output := by
  cases pattern with
  | Empty =>
    refine ⟨some .Empty,?_,?_,?_⟩
    · rw [indexed.reconstruct_embedding]
    · exact empty_retains (model input)
    · rfl
  | Pair ph pt =>
    cases input with
    | Empty =>
      refine ⟨none,?_,?_⟩
      · rw [indexed.reconstruct_embedding]
      · intro he
        have hb := dyckEmbeds_semilength_le he
        simp only [toDyck,model,erase,DyckWord.semilength_zero,DyckWord.semilength_add,DyckWord.semilength_nest] at hb
        omega
    | Pair index head tail =>
      obtain ⟨inside,hInside,hInsidePost⟩ := reconstruct_embedding_refines ph head
      cases inside with
      | none =>
        obtain ⟨output,hOutput,hOutputPost⟩ := reconstruct_embedding_refines (.Pair ph pt) (appendWord head tail)
        refine ⟨output,?_,fallback_outcome ph pt index head tail output (Or.inl hInsidePost) hOutputPost⟩
        rw [indexed.reconstruct_embedding]
        simp only [hInside,bind_ok,append_indexed_correct,hOutput]
      | some inside =>
        obtain ⟨outside,hOutside,hOutsidePost⟩ := reconstruct_embedding_refines pt tail
        cases outside with
        | none =>
          obtain ⟨output,hOutput,hOutputPost⟩ := reconstruct_embedding_refines (.Pair ph pt) (appendWord head tail)
          refine ⟨output,?_,fallback_outcome ph pt index head tail output (Or.inr hOutsidePost) hOutputPost⟩
          rw [indexed.reconstruct_embedding]
          simp only [hInside,hOutside,bind_ok,append_indexed_correct,hOutput]
        | some outside =>
          obtain ⟨hInsideRetains,hInsideShape⟩ := hInsidePost
          obtain ⟨hOutsideRetains,hOutsideShape⟩ := hOutsidePost
          refine ⟨some (.Pair index inside outside),?_,?_,?_⟩
          · rw [indexed.reconstruct_embedding]
            simp only [hInside,hOutside,bind_ok]
          · exact Retains.keep index.val hInsideRetains hOutsideRetains
          · simp only [model,erase,toDyck,hInsideShape,hOutsideShape]
termination_by (toDyck pattern).semilength + (erase (model input)).semilength
decreasing_by
  all_goals subst_vars
  all_goals simp only [toDyck,model,erase,model_appendWord,erase_append,DyckWord.semilength_add,DyckWord.semilength_nest]
  all_goals omega

/-- Every independently feasible shape is successfully reconstructed in the
original indexed input; failure and divergence are excluded by the source proof. -/
theorem reconstruct_embedding_success (pattern : BalancedWord) (input : indexed.IndexedWord)
    (h : DyckEmbeds (toDyck pattern) (erase (model input))) :
    ∃ result, indexed.reconstruct_embedding pattern input = .ok (some result) ∧
      Retains (model result) (model input) ∧ erase (model result) = toDyck pattern := by
  obtain ⟨output,hRun,hOutcome⟩ := reconstruct_embedding_refines pattern input
  cases output with
  | none => exact False.elim (hOutcome h)
  | some result => exact ⟨result,hRun,hOutcome⟩

/-- Conversely an actual rejection certifies independent infeasibility. -/
theorem reconstruct_embedding_none_iff (pattern : BalancedWord) (input : indexed.IndexedWord) :
    indexed.reconstruct_embedding pattern input = .ok none ↔ ¬ DyckEmbeds (toDyck pattern) (erase (model input)) := by
  obtain ⟨output,hRun,hOutcome⟩ := reconstruct_embedding_refines pattern input
  rw [hRun]
  cases output with
  | none => exact ⟨fun _ => hOutcome,fun _ => rfl⟩
  | some result =>
    constructor
    · intro he
      cases (Result.ok_injective he)
    · intro hn
      have hb := hOutcome.1.erase_embeds
      rw [hOutcome.2] at hb
      exact False.elim (hn hb)

end SubtreeProofs.Rust.IndexedOrderedSolver

end
