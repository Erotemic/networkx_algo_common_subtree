module

public import SubtreeProofs.Rust.OrderedSolver
public import SubtreeProofs.Paper2004.IsomorphismScores
import Mathlib.Tactic

/-! # Structural Rust words as independent ordered child forests -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.OrderedIsomorphism

open Paper2004.OrderedTree OrderedSolver

/-- Structural first-child/next-sibling interpretation, independent of solvers. -/
def toForest : BalancedWord → List Paper2004.OrderedTree
  | .Empty => []
  | .Pair head tail => .node (toForest head)::toForest tail

@[simp] theorem toForest_encode (word : BalancedWord) :
    encodeForestDyck (toForest word) = toDyck word := by
  induction word with
  | Empty => rfl
  | Pair head tail ihHead ihTail =>
    simp only [toForest,encodeForestDyck,encodeDyck,toDyck,ihHead,ihTail]

@[simp] theorem toForest_edges (word : BalancedWord) :
    forestEdgeCount (toForest word) = (toDyck word).semilength := by
  have h := encodeForestDyck_semilength (toForest word)
  rw [toForest_encode] at h
  exact h.symm

/-- The new structural forest interpretation agrees with the established
independent two-sided Dyck/tree representation bridge. -/
theorem toForest_decode (word : BalancedWord) :
    toForest word = decodeForestDyck (toDyck word) := by
  rw [← toForest_encode word,decodeForestDyck_encodeForestDyck]

theorem toTree_decode (word : BalancedWord) :
    decodeDyck (toDyck word) = .node (toForest word) := by
  rw [decodeDyck_eq_node_decodeForestDyck,← toForest_decode]

/-- Exact scores make the actual source tie choice agree with forest choice. -/
theorem selectResult_forest (first second : CommonEmbedding)
    (hf : first.edges.val = forestEdgeCount (toForest first.word))
    (hs : second.edges.val = forestEdgeCount (toForest second.word)) :
    toForest (selectResult first second).word = OrderedIsoDP.longer (toForest first.word) (toForest second.word) := by
  unfold selectResult OrderedIsoDP.longer
  change toForest (if first.edges.val < second.edges.val then second else first).word = _
  simp only [hf,hs]
  split <;> rfl

theorem selectResult_edges (first second : CommonEmbedding)
    (hf : first.edges.val = forestEdgeCount (toForest first.word))
    (hs : second.edges.val = forestEdgeCount (toForest second.word)) :
    (selectResult first second).edges.val = forestEdgeCount (toForest (selectResult first second).word) := by
  unfold selectResult
  split
  · exact hs
  · exact hf

end SubtreeProofs.Rust.OrderedIsomorphism

end
