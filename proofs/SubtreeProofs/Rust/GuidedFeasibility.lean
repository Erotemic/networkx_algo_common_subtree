module

public import SubtreeProofs.Rust.MemoizedOrderedSolver
public import SubtreeProofs.Rust.IndexedWordRepresentation
public import SubtreeProofs.Paper2004.EmbeddingFeasibility
import Mathlib.Tactic

/-! # Actual shared-memo feasibility checks for indexed reconstruction -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.GuidedReconstruction

open OrderedSolver IndexedOrderedSolver MemoizedOrderedSolver Paper2004.OrderedTree Paper2004.IndexedWord

/-- The structural shape represented by an actual original-index word. -/
def eraseWord : indexed.IndexedWord → BalancedWord
  | .Empty => .Empty
  | .Pair _ head tail => .Pair (eraseWord head) (eraseWord tail)

@[simp] theorem toDyck_eraseWord (word : indexed.IndexedWord) : toDyck (eraseWord word) = erase (model word) := by
  induction word with
  | Empty => rfl
  | Pair index head tail ihHead ihTail => simp only [eraseWord,toDyck,model,erase,ihHead,ihTail]

/-- Actual shape erasure preserves every pair and the full nesting. -/
theorem erase_indexed_correct (word : indexed.IndexedWord) : guided.erase_indexed word = .ok (eraseWord word) := by
  induction word with
  | Empty => rw [guided.erase_indexed]; rfl
  | Pair index head tail ihHead ihTail =>
    rw [guided.erase_indexed,ihHead,bind_ok,ihTail,bind_ok]
    rfl

/-- The actual source guard is true precisely for an independently feasible
pattern, while threading a sound shared memo table. No feasibility oracle is
assumed: the guard runs the proved memoized optimizer and structural equality. -/
theorem embedding_possible_spec (pattern : BalancedWord) (input : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hp : (toDyck pattern).semilength < 2^32)
    (hi : (erase (model input)).semilength < 2^32) :
    guided.embedding_possible pattern input table ⦃ answer output => ∃ possible,
      answer = some possible ∧ TableSound output ∧
      (possible = true ↔ DyckEmbeds (toDyck pattern) (erase (model input))) ⦄ := by
  obtain ⟨matching,output,hRun,hm,ho,_⟩ := memoized_common_embedding_refines pattern (eraseWord input) table hs hp (by simpa only [toDyck_eraseWord] using hi)
  unfold guided.embedding_possible
  simp only [erase_indexed_correct,bind_ok,hRun,words_equal_correct]
  apply (WP.spec_ok _).mpr
  refine ⟨decide (matching.word = pattern),rfl,ho,?_⟩
  rw [decide_eq_true_eq,← toDyck_eq_iff,hm.1,toDyck_eraseWord,paperCommon_eq_left_iff]

/-- The actual two-piece guard selects retention precisely when both pieces
are independently feasible, and preserves the shared memo invariant. -/
theorem keep_first_pair_spec (ph pt : BalancedWord) (head tail : indexed.IndexedWord) (table : RustMemo)
    (hs : TableSound table) (hph : (toDyck ph).semilength < 2^32) (hpt : (toDyck pt).semilength < 2^32)
    (hh : (erase (model head)).semilength < 2^32) (ht : (erase (model tail)).semilength < 2^32) :
    guided.keep_first_pair ph pt head tail table ⦃ answer output => ∃ possible,
      answer = some possible ∧ TableSound output ∧
      (possible = true ↔ DyckEmbeds (toDyck ph) (erase (model head)) ∧ DyckEmbeds (toDyck pt) (erase (model tail))) ⦄ := by
  unfold guided.keep_first_pair
  apply WP.spec_bind (embedding_possible_spec ph head table hs hph hh)
  rintro ⟨answer,headCache⟩ ⟨possible,hAnswer,hSound,hPossible⟩
  subst answer
  cases possible with
  | false =>
    apply (WP.spec_ok _).mpr
    refine ⟨false,rfl,hSound,?_⟩
    have hn : ¬ DyckEmbeds (toDyck ph) (erase (model head)) := by simpa only [Bool.false_eq_true,false_iff] using hPossible
    simp only [Bool.false_eq_true,hn,false_and]
  | true =>
    have hy := hPossible.mp rfl
    apply WP.spec_mono (embedding_possible_spec pt tail headCache hSound hpt ht)
    rintro ⟨answer,output⟩ ⟨possible,hAnswer,hSound,hPossible⟩
    refine ⟨possible,hAnswer,hSound,?_⟩
    simpa only [hy,true_and] using hPossible

end SubtreeProofs.Rust.GuidedReconstruction

end
