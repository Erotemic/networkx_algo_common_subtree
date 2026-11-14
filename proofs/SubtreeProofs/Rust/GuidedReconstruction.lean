module

public import SubtreeProofs.Rust.GuidedFeasibility
public import SubtreeProofs.Rust.IndexedReconstructionSpecification
import Mathlib.Tactic

/-! # Actual guided reconstruction: complete original indices and a linear call bound -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- The concrete source counter's checked addition succeeds under its exact
u64 mathematical bound. -/
theorem checked_add64_success (first second : U64) (h : first.val+second.val < 2^64) :
    ∃ result, U64.checked_add first second = some result ∧ result.val = first.val+second.val := by
  have hs := U64.checked_add_bv_spec first second
  cases hc : U64.checked_add first second with
  | none =>
    rw [hc] at hs
    have hm : U64.max = 2^64-1 := by rw [U64.max_eq]; norm_num
    rw [hm] at hs
    omega
  | some result =>
    rw [hc] at hs
    exact ⟨result,rfl,hs.2.1⟩

/-- Full source outcome, sound memo preservation and the actual recorded number
of recursive reconstruction calls. Feasibility computations have their own memo
costs and are not included in this witness-call counter. -/
def GuidedOutcome (pattern : BalancedWord) (input : indexed.IndexedWord) (result : guided.GuidedReconstruction) : Prop :=
  ReconstructionOutcome pattern input result.word ∧ TableSound result.table ∧
    result.calls.val ≤ 2*(erase (model input)).semilength+1

/-- Every bounded represented pattern/input pair terminates with a genuine
indexed contraction of exactly the pattern, or complete independent rejection.
Its actual source call counter is at most twice the original input pairs plus
one, and its threaded memo remains sound. -/
theorem reconstruct_guided_spec (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hp : (toDyck pattern).semilength < 2^32)
    (hi : (erase (model input)).semilength < 2^32) :
    guided.reconstruct_guided pattern input table ⦃ output => ∃ result,
      output = some result ∧ GuidedOutcome pattern input result ⦄ := by
  cases pattern with
  | Empty =>
    rw [guided.reconstruct_guided]
    apply (WP.spec_ok _).mpr
    refine ⟨⟨some .Empty,table,1#u64⟩,rfl,?_,hs,?_⟩
    · exact ⟨empty_retains (model input),rfl⟩
    · change 1 ≤ 2*(erase (model input)).semilength+1
      omega
  | Pair ph pt =>
    have hpSize := hp
    simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest] at hpSize
    cases input with
    | Empty =>
      rw [guided.reconstruct_guided]
      apply (WP.spec_ok _).mpr
      refine ⟨⟨none,table,1#u64⟩,rfl,?_,hs,by change 1 ≤ 1; decide⟩
      intro he
      have hb := dyckEmbeds_semilength_le he
      simp only [toDyck,model,erase,DyckWord.semilength_zero,DyckWord.semilength_add,DyckWord.semilength_nest] at hb
      omega
    | Pair index head tail =>
      have hiSize := hi
      simp only [model,erase,DyckWord.semilength_add,DyckWord.semilength_nest] at hiSize
      unfold guided.reconstruct_guided
      apply WP.spec_bind (keep_first_pair_spec ph pt head tail table hs (by omega) (by omega) (by omega) (by omega))
      rintro ⟨answer,cache⟩ ⟨keep,hAnswer,hSound,hKeep⟩
      subst answer
      cases keep with
      | false =>
        have hReject : ¬ DyckEmbeds (toDyck ph) (erase (model head)) ∨ ¬ DyckEmbeds (toDyck pt) (erase (model tail)) := by
          have hn := hKeep.not.mp (by decide)
          exact not_and_or.mp hn
        rw [append_indexed_correct]
        simp only [bind_ok]
        apply WP.spec_bind (reconstruct_guided_spec (.Pair ph pt) (appendWord head tail) cache hSound hp
          (by simp only [model_appendWord,erase_append,DyckWord.semilength_add]; omega))
        rintro output ⟨result,hOutput,hPost,hResultSound,hCount⟩
        subst output
        have hc := hCount
        simp only [model_appendWord,erase_append,DyckWord.semilength_add] at hc
        obtain ⟨calls,hCalls,hCallsValue⟩ := checked_add64_success result.calls 1#u64 (by scalar_tac)
        simp only [lift,hCalls,bind_ok]
        apply (WP.spec_ok _).mpr
        refine ⟨{ result with calls := calls },rfl,fallback_outcome ph pt index head tail result.word hReject hPost,hResultSound,?_⟩
        simp only [model,erase,DyckWord.semilength_add,DyckWord.semilength_nest]
        have hone : (1#u64).val = 1 := rfl
        omega
      | true =>
        obtain ⟨hHeadFeasible,hTailFeasible⟩ := hKeep.mp rfl
        apply WP.spec_bind (reconstruct_guided_spec ph head cache hSound (by omega) (by omega))
        rintro output ⟨inside,hOutput,hInside,hInsideSound,hInsideCount⟩
        subst output
        cases hInsideWord : inside.word with
        | none =>
          have hn : ¬ DyckEmbeds (toDyck ph) (erase (model head)) := by simpa only [hInsideWord,ReconstructionOutcome] using hInside
          exact False.elim (hn hHeadFeasible)
        | some insideWord =>
          simp only [hInsideWord]
          apply WP.spec_bind (reconstruct_guided_spec pt tail inside.table hInsideSound (by omega) (by omega))
          rintro output ⟨outside,hOutput,hOutside,hOutsideSound,hOutsideCount⟩
          subst output
          cases hOutsideWord : outside.word with
          | none =>
            have hn : ¬ DyckEmbeds (toDyck pt) (erase (model tail)) := by simpa only [hOutsideWord,ReconstructionOutcome] using hOutside
            exact False.elim (hn hTailFeasible)
          | some outsideWord =>
            simp only [hOutsideWord]
            obtain ⟨subtotal,hSubtotal,hSubtotalValue⟩ := checked_add64_success inside.calls outside.calls (by omega)
            obtain ⟨calls,hCalls,hCallsValue⟩ := checked_add64_success subtotal 1#u64 (by scalar_tac)
            simp only [lift,hSubtotal,hCalls,bind_ok]
            apply (WP.spec_ok _).mpr
            have hh : Retains (model insideWord) (model head) ∧ erase (model insideWord) = toDyck ph := by
              simpa only [hInsideWord,ReconstructionOutcome] using hInside
            have ht : Retains (model outsideWord) (model tail) ∧ erase (model outsideWord) = toDyck pt := by
              simpa only [hOutsideWord,ReconstructionOutcome] using hOutside
            refine ⟨{ outside with word := some (.Pair index insideWord outsideWord),calls := calls },rfl,?_,hOutsideSound,?_⟩
            · exact ⟨Retains.keep index.val hh.1 ht.1,by simp only [model,erase,toDyck,hh.2,ht.2]⟩
            · simp only [model,erase,DyckWord.semilength_add,DyckWord.semilength_nest]
              have hone : (1#u64).val = 1 := rfl
              omega
termination_by (erase (model input)).semilength
decreasing_by
  all_goals subst_vars
  all_goals simp only [model,erase,model_appendWord,erase_append,DyckWord.semilength_add,DyckWord.semilength_nest]
  all_goals omega

/-- Independently feasible inputs return an actual indexed witness, preserving
both the shared cache and the concrete linear reconstruction-call bound. -/
theorem reconstruct_guided_success_spec (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hp : (toDyck pattern).semilength < 2^32)
    (hi : (erase (model input)).semilength < 2^32)
    (hf : DyckEmbeds (toDyck pattern) (erase (model input))) :
    guided.reconstruct_guided pattern input table ⦃ output => ∃ result word,
      output = some result ∧ result.word = some word ∧ Retains (model word) (model input) ∧
      erase (model word) = toDyck pattern ∧ TableSound result.table ∧
      result.calls.val ≤ 2*(erase (model input)).semilength+1 ⦄ := by
  apply WP.spec_mono (reconstruct_guided_spec pattern input table hs hp hi)
  rintro output ⟨result,hOutput,hPost,hSound,hCount⟩
  cases hWord : result.word with
  | none =>
    have hn : ¬ DyckEmbeds (toDyck pattern) (erase (model input)) := by simpa only [hWord,ReconstructionOutcome] using hPost
    exact False.elim (hn hf)
  | some word =>
    have hh : Retains (model word) (model input) ∧ erase (model word) = toDyck pattern := by
      simpa only [hWord,ReconstructionOutcome] using hPost
    exact ⟨result,word,hOutput,hWord,hh.1,hh.2,hSound,hCount⟩

end SubtreeProofs.Rust.GuidedReconstruction

end
