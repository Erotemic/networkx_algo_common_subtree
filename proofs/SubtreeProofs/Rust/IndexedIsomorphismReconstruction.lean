module

public import SubtreeProofs.Rust.IndexedWordNumbering
public import SubtreeProofs.Rust.OrderedArbitraryIsomorphism
public import SubtreeProofs.Paper2004.AnnotatedIsomorphism
import Mathlib.Tactic

/-! # Actual original-index isomorphism reconstruction, both parent policies -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedIsomorphism

open IndexedOrderedSolver OrderedSolver OrderedIsomorphism Paper2004.OrderedTree

def forest : indexed.IndexedWord → List Paper2004.OrderedTree
  | .Empty => []
  | .Pair _ head tail => .node (forest head) :: forest tail

theorem forest_model (word : indexed.IndexedWord) : forest word = Paper2004.AnnotatedIso.erase (model word) := by
  induction word with
  | Empty => rfl
  | Pair index head tail ihHead ihTail => simp only [forest,model,Paper2004.AnnotatedIso.erase,ihHead,ihTail]

theorem forest_encode (word : indexed.IndexedWord) :
    encodeForestDyck (forest word) = Paper2004.IndexedWord.erase (model word) := by
  induction word with
  | Empty => rfl
  | Pair index head tail ihHead ihTail =>
    simp only [forest,encodeForestDyck,encodeDyck,model,Paper2004.IndexedWord.erase,ihHead,ihTail]

theorem forest_decode (word : indexed.IndexedWord) :
    forest word = decodeForestDyck (Paper2004.IndexedWord.erase (model word)) := by
  rw [← forest_encode,decodeForestDyck_encodeForestDyck]

def RootedOutcome (pattern : BalancedWord) (input : indexed.IndexedWord) : Option indexed.IndexedWord → Prop
  | some result => Paper2004.AnnotatedIso.Prunes (model result) (model input) ∧ forest result = toForest pattern
  | none => ¬ ForestPrunes (toForest pattern) (forest input)

theorem rooted_fallback (ph pt : BalancedWord) (index : U32) (head tail : indexed.IndexedWord)
    (output : Option indexed.IndexedWord)
    (hRejected : ¬ ForestPrunes (toForest ph) (forest head) ∨ ¬ ForestPrunes (toForest pt) (forest tail))
    (h : RootedOutcome (.Pair ph pt) tail output) : RootedOutcome (.Pair ph pt) (.Pair index head tail) output := by
  cases output with
  | some result =>
    refine ⟨?_,h.2⟩
    exact (Paper2004.AnnotatedIso.Select.skip index.val (model head) h.1.select).prunes
  | none =>
    intro hFeasible
    rcases hFeasible.first with hDrop | ⟨hHead,hTail⟩
    · exact h hDrop
    · rcases hRejected with hNoHead | hNoTail
      · exact hNoHead hHead.children
      · exact hNoTail hTail

/-- Total source reconstruction: return a genuine indexed whole-subtree
pruning of exactly the pattern, or certify independent rooted infeasibility. -/
theorem reconstruct_rooted_refines (pattern : BalancedWord) (input : indexed.IndexedWord) :
    ∃ output, indexed_isomorphism.reconstruct_rooted_isomorphism pattern input = .ok output ∧
      RootedOutcome pattern input output := by
  cases pattern with
  | Empty =>
    refine ⟨some .Empty,?_,?_,rfl⟩
    · rw [indexed_isomorphism.reconstruct_rooted_isomorphism]
    · exact Paper2004.AnnotatedIso.Prunes.empty _
  | Pair ph pt =>
    cases input with
    | Empty =>
      refine ⟨none,?_,?_⟩
      · rw [indexed_isomorphism.reconstruct_rooted_isomorphism]
      · intro h
        have he := h.eq_nil_of_nil
        simp [toForest] at he
    | Pair index head tail =>
      obtain ⟨inside,hInside,hInsidePost⟩ := reconstruct_rooted_refines ph head
      cases inside with
      | none =>
        obtain ⟨output,hOutput,hPost⟩ := reconstruct_rooted_refines (.Pair ph pt) tail
        refine ⟨output,?_,rooted_fallback ph pt index head tail output (Or.inl hInsidePost) hPost⟩
        rw [indexed_isomorphism.reconstruct_rooted_isomorphism]
        simp only [hInside,bind_ok,hOutput]
      | some inside =>
        obtain ⟨outside,hOutside,hOutsidePost⟩ := reconstruct_rooted_refines pt tail
        cases outside with
        | none =>
          obtain ⟨output,hOutput,hPost⟩ := reconstruct_rooted_refines (.Pair ph pt) tail
          refine ⟨output,?_,rooted_fallback ph pt index head tail output (Or.inr hOutsidePost) hPost⟩
          rw [indexed_isomorphism.reconstruct_rooted_isomorphism]
          simp only [hInside,hOutside,bind_ok,hOutput]
        | some outside =>
          refine ⟨some (.Pair index inside outside),?_,?_,?_⟩
          · rw [indexed_isomorphism.reconstruct_rooted_isomorphism]
            simp only [hInside,hOutside,bind_ok]
          · exact (Paper2004.AnnotatedIso.Select.keep hInsidePost.1.select hOutsidePost.1.select).prunes
          · simp only [forest,toForest,hInsidePost.2,hOutsidePost.2]
termination_by (model input).numNodes
decreasing_by all_goals simp only [model,BinaryTree.numNodes]; omega

def AnyOutcome (pattern : BalancedWord) (input : indexed.IndexedWord) : Option indexed.IndexedWord → Prop
  | some result => Paper2004.AnnotatedIso.AnyPrunes (model result) (model input) ∧ forest result = toForest pattern
  | none => ¬ IsomorphicSubtree (.node (toForest pattern)) (.node (forest input))

theorem singleton_rooted {candidate : Paper2004.OrderedTree} (h : IsomorphicSubtree candidate (.node [])) :
    RootPrunes candidate (.node []) := by
  obtain ⟨root,hRoot,hPrunes⟩ := h
  cases hRoot with
  | refl => exact hPrunes
  | step hMember _ => cases hMember

/-- Total arbitrary-parent reconstruction preserves original labels and
certifies independent infeasibility when all actual regions are rejected. -/
theorem reconstruct_any_refines (pattern : BalancedWord) (input : indexed.IndexedWord) :
    ∃ output, indexed_isomorphism.reconstruct_any_isomorphism pattern input = .ok output ∧
      AnyOutcome pattern input output := by
  obtain ⟨rooted,hRooted,hRootedPost⟩ := reconstruct_rooted_refines pattern input
  cases rooted with
  | some result =>
    refine ⟨some result,?_,hRootedPost.1.any,hRootedPost.2⟩
    rw [indexed_isomorphism.reconstruct_any_isomorphism.eq_def]
    simp only [hRooted,bind_ok]
  | none =>
    cases input with
    | Empty =>
      refine ⟨none,?_,?_⟩
      · rw [indexed_isomorphism.reconstruct_any_isomorphism.eq_def]
        simp only [hRooted,bind_ok]
      · intro h
        exact hRootedPost (singleton_rooted h).children
    | Pair index head tail =>
      obtain ⟨inside,hInside,hInsidePost⟩ := reconstruct_any_refines pattern head
      cases inside with
      | some result =>
        refine ⟨some result,?_,hInsidePost.1.head index.val (model tail),hInsidePost.2⟩
        rw [indexed_isomorphism.reconstruct_any_isomorphism.eq_def]
        simp only [hRooted,hInside,bind_ok]
      | none =>
        obtain ⟨outside,hOutside,hOutsidePost⟩ := reconstruct_any_refines pattern tail
        refine ⟨outside,?_,?_⟩
        · rw [indexed_isomorphism.reconstruct_any_isomorphism.eq_def]
          simp only [hRooted,hInside,hOutside,bind_ok]
        · cases outside with
          | some result => exact ⟨hOutsidePost.1.tail index.val (model head),hOutsidePost.2⟩
          | none =>
            intro h
            rcases h.first with hHere | hHead | hTail
            · exact hRootedPost hHere.children
            · exact hInsidePost hHead
            · exact hOutsidePost hTail
termination_by (model input).numNodes
decreasing_by all_goals simp only [model,BinaryTree.numNodes]; omega

theorem reconstruct_rooted_success (pattern : BalancedWord) (input : indexed.IndexedWord)
    (h : ForestPrunes (toForest pattern) (forest input)) :
    ∃ result, indexed_isomorphism.reconstruct_rooted_isomorphism pattern input = .ok (some result) ∧
      Paper2004.AnnotatedIso.Prunes (model result) (model input) ∧ forest result = toForest pattern := by
  obtain ⟨output,hRun,hPost⟩ := reconstruct_rooted_refines pattern input
  cases output with
  | none => exact False.elim (hPost h)
  | some result => exact ⟨result,hRun,hPost⟩

theorem reconstruct_any_success (pattern : BalancedWord) (input : indexed.IndexedWord)
    (h : IsomorphicSubtree (.node (toForest pattern)) (.node (forest input))) :
    ∃ result, indexed_isomorphism.reconstruct_any_isomorphism pattern input = .ok (some result) ∧
      Paper2004.AnnotatedIso.AnyPrunes (model result) (model input) ∧ forest result = toForest pattern := by
  obtain ⟨output,hRun,hPost⟩ := reconstruct_any_refines pattern input
  cases output with
  | none => exact False.elim (hPost h)
  | some result => exact ⟨result,hRun,hPost⟩

end SubtreeProofs.Rust.IndexedIsomorphism

end
