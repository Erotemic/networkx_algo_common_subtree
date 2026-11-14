module

public import SubtreeProofs.Rust.GuidedReconstruction
public import SubtreeProofs.Paper2004.MemoGrowth
import Mathlib.Tactic

/-! # Actual shared-memo growth across guided feasibility and witness calls -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- Every actual feasibility computation adds only keys from its own independent
pattern/input decomposition family and preserves old key uniqueness. -/
theorem embedding_possible_growth_spec (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hp : (toDyck pattern).semilength < 2^32)
    (hi : (erase (model input)).semilength < 2^32) :
    guided.embedding_possible pattern input table ⦃ _ output =>
      TableSound output ∧ MemoGrowth (MemoDomain (toDyck pattern) (erase (model input))) (numericMemo table) (numericMemo output) ⦄ := by
  obtain ⟨matching,output,hRun,_,ho,hNumeric⟩ := memoized_common_embedding_refines pattern (eraseWord input) table hs hp (by simpa only [toDyck_eraseWord] using hi)
  unfold guided.embedding_possible
  simp only [erase_indexed_correct,bind_ok,hRun,words_equal_correct]
  apply (WP.spec_ok _).mpr
  refine ⟨ho,?_⟩
  rw [hNumeric,toDyck_eraseWord]
  exact memoLcs_growth _ _ _

/-- The actual two-piece guard grows only the enclosing pattern/input product;
its second query shares the first query's real updated table. -/
theorem keep_first_pair_growth_spec (ph pt : BalancedWord) (head tail : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hph : (toDyck ph).semilength < 2^32) (hpt : (toDyck pt).semilength < 2^32)
    (hh : (erase (model head)).semilength < 2^32) (ht : (erase (model tail)).semilength < 2^32) :
    guided.keep_first_pair ph pt head tail table ⦃ _ output => TableSound output ∧
      MemoGrowth (MemoDomain (toDyck (.Pair ph pt)) (erase (model (.Pair 0#u32 head tail)))) (numericMemo table) (numericMemo output) ⦄ := by
  have hd := memoDomain_components (toDyck ph) (toDyck pt) (erase (model head)) (erase (model tail))
  unfold guided.keep_first_pair
  apply WP.spec_bind (embedding_possible_growth_spec ph head table hs hph hh)
  rintro ⟨answer,headCache⟩ ⟨hSound,hGrowth⟩
  have hHead := hGrowth.decomposition hd.1
  cases answer with
  | none =>
    apply (WP.spec_ok _).mpr
    exact ⟨hSound,hHead⟩
  | some possible =>
    cases possible with
    | false =>
      apply (WP.spec_ok _).mpr
      exact ⟨hSound,hHead⟩
    | true =>
      apply WP.spec_mono (embedding_possible_growth_spec pt tail headCache hSound hpt ht)
      rintro ⟨answer,output⟩ ⟨hOutputSound,hTail⟩
      exact ⟨hOutputSound,hHead.trans (hTail.decomposition hd.2.1)⟩

/-- Growth of a successful concrete helper result. Rejection branches carry no
returned table; functional totality is proved separately by the stronger source
outcome theorem and can be conjoined with this property. -/
def CacheOutcome (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (output : Option guided.GuidedReconstruction) : Prop :=
  match output with
  | none => True
  | some result => TableSound result.table ∧
      MemoGrowth (MemoDomain (toDyck pattern) (erase (model input))) (numericMemo table) (numericMemo result.table)

/-- All actual feasibility and recursive reconstruction calls add only keys
from the enclosing decomposition product. This covers every successful return
and preserves uniqueness even when the initial memo contains other families. -/
theorem reconstruct_guided_growth_spec (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hp : (toDyck pattern).semilength < 2^32)
    (hi : (erase (model input)).semilength < 2^32) :
    guided.reconstruct_guided pattern input table ⦃ output => CacheOutcome pattern input table output ⦄ := by
  cases pattern with
  | Empty =>
    rw [guided.reconstruct_guided]
    apply (WP.spec_ok _).mpr
    exact ⟨hs,MemoGrowth.refl _ _⟩
  | Pair ph pt =>
    have hpSize := hp
    simp only [toDyck,DyckWord.semilength_add,DyckWord.semilength_nest] at hpSize
    cases input with
    | Empty =>
      rw [guided.reconstruct_guided]
      apply (WP.spec_ok _).mpr
      exact ⟨hs,MemoGrowth.refl _ _⟩
    | Pair index head tail =>
      have hiSize := hi
      simp only [model,erase,DyckWord.semilength_add,DyckWord.semilength_nest] at hiSize
      have hd := memoDomain_components (toDyck ph) (toDyck pt) (erase (model head)) (erase (model tail))
      unfold guided.reconstruct_guided
      apply WP.spec_bind (keep_first_pair_growth_spec ph pt head tail table hs (by omega) (by omega) (by omega) (by omega))
      rintro ⟨answer,cache⟩ ⟨hSound,hGuard⟩
      cases answer with
      | none =>
        apply (WP.spec_ok _).mpr
        trivial
      | some keep =>
        cases keep with
        | false =>
          rw [append_indexed_correct]
          simp only [bind_ok]
          apply WP.spec_bind (reconstruct_guided_growth_spec (.Pair ph pt) (appendWord head tail) cache hSound hp
            (by simp only [model_appendWord,erase_append,DyckWord.semilength_add]; omega))
          intro output hPost
          cases output with
          | none =>
            apply (WP.spec_ok _).mpr
            trivial
          | some result =>
            have hg : MemoGrowth (MemoDomain (toDyck (.Pair ph pt)) (erase (model (.Pair index head tail))))
                (numericMemo table) (numericMemo result.table) :=
              hGuard.trans (hPost.2.decomposition (by simpa only [toDyck,model,erase,model_appendWord,erase_append] using hd.2.2))
            cases hCalls : U64.checked_add result.calls 1#u64 with
            | none => simp only [lift,hCalls,bind_ok,WP.spec_ok,CacheOutcome]
            | some calls =>
              simp only [lift,hCalls,bind_ok]
              apply (WP.spec_ok _).mpr
              exact ⟨hPost.1,hg⟩
        | true =>
          apply WP.spec_bind (reconstruct_guided_growth_spec ph head cache hSound (by omega) (by omega))
          intro output hInside
          cases output with
          | none =>
            apply (WP.spec_ok _).mpr
            trivial
          | some inside =>
            cases hWord : inside.word with
            | none =>
              simp only [hWord]
              apply (WP.spec_ok _).mpr
              trivial
            | some insideWord =>
              simp only [hWord]
              have hFirst := hGuard.trans (hInside.2.decomposition hd.1)
              apply WP.spec_bind (reconstruct_guided_growth_spec pt tail inside.table hInside.1 (by omega) (by omega))
              intro output hOutside
              cases output with
              | none =>
                apply (WP.spec_ok _).mpr
                trivial
              | some outside =>
                cases hWord : outside.word with
                | none =>
                  simp only [hWord]
                  apply (WP.spec_ok _).mpr
                  trivial
                | some outsideWord =>
                  simp only [hWord]
                  have hFinal := hFirst.trans (hOutside.2.decomposition hd.2.1)
                  cases hSum : U64.checked_add inside.calls outside.calls with
                  | none => simp only [lift,bind_ok,WP.spec_ok,CacheOutcome]
                  | some subtotal =>
                    simp only [lift,bind_ok]
                    cases hCalls : U64.checked_add subtotal 1#u64 with
                    | none => simp only [WP.spec_ok,CacheOutcome]
                    | some calls =>
                      apply (WP.spec_ok _).mpr
                      exact ⟨hOutside.1,hFinal⟩
termination_by (erase (model input)).semilength
decreasing_by
  all_goals subst_vars
  all_goals simp only [model,erase,model_appendWord,erase_append,DyckWord.semilength_add,DyckWord.semilength_nest]
  all_goals omega

end SubtreeProofs.Rust.GuidedReconstruction

end
