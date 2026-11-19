module

public import SubtreeProofs.Paper2004.IndexedWord
import Mathlib.Tactic

/-! # Canonical original pair positions and independently maximum indexed witnesses -/

@[expose] public section

namespace SubtreeProofs.Paper2004.IndexedWord

open OrderedTree

/-- Assign the actual opening/preorder positions of a binary child forest. -/
def numberFrom : BinaryTree Unit → Nat → Word
  | .nil,_ => .nil
  | .node _ head tail,start => .node start (numberFrom head (start+1)) (numberFrom tail (start+1+head.numNodes))

@[simp] theorem erase_numberFrom (shape : BinaryTree Unit) (start : Nat) :
    erase (numberFrom shape start) = DyckWord.ofTree shape := by
  induction shape generalizing start with
  | nil => rfl
  | node _ head tail ihHead ihTail => simp only [numberFrom,erase,DyckWord.ofTree,ihHead,ihTail]

@[simp] theorem indices_numberFrom (shape : BinaryTree Unit) (start : Nat) :
    indices (numberFrom shape start) = List.range' start shape.numNodes := by
  induction shape generalizing start with
  | nil => rfl
  | node _ head tail ihHead ihTail =>
    simp only [numberFrom,indices,ihHead,ihTail,BinaryTree.numNodes]
    rw [List.range'_append_1,List.range'_succ]

/-- Pair identities of the independently specified original ordered tree,
numbered from zero in its established edge encoding. -/
def canonical (tree : OrderedTree) : Word := numberFrom tree.encodeDyck.toTree 0

@[simp] theorem canonical_erase (tree : OrderedTree) : erase (canonical tree) = tree.encodeDyck := by
  simp only [canonical,erase_numberFrom,DyckWord.ofTree_toTree]

@[simp] theorem canonical_indices (tree : OrderedTree) : indices (canonical tree) = List.range tree.edgeCount := by
  simp only [canonical,indices_numberFrom,DyckWord.numNodes_toTree,encodeDyck_semilength,List.range_eq_range']

/-- Independent optimal indexed contraction witness: two actual original
pair deletions, the same surviving shape, a maximum common contracted tree,
and exactly its edge score. No solver occurs in this definition. -/
def IndexedMaximum (left right : OrderedTree) (leftWitness rightWitness : Word) (score : Nat) : Prop :=
  Retains leftWitness (canonical left) ∧ Retains rightWitness (canonical right) ∧
    erase leftWitness = erase rightWitness ∧
    IsMaximumCommon (decodeDyck (erase leftWitness)) left right ∧ score = (decodeDyck (erase leftWitness)).edgeCount

/-- An indexed optimum uses distinct genuine original input indices in their
original order. These properties follow from the operational witness relation. -/
theorem IndexedMaximum.indices_valid {left right : OrderedTree} {leftWitness rightWitness : Word} {score : Nat}
    (h : IndexedMaximum left right leftWitness rightWitness score) :
    (indices leftWitness).Nodup ∧ (indices rightWitness).Nodup ∧
      (∀ index ∈ indices leftWitness, index < left.edgeCount) ∧
      (∀ index ∈ indices rightWitness, index < right.edgeCount) := by
  refine ⟨h.1.indices_nodup ?_,h.2.1.indices_nodup ?_,?_,?_⟩
  · rw [canonical_indices]
    exact List.nodup_range
  · rw [canonical_indices]
    exact List.nodup_range
  · exact fun index hi => h.1.index_lt left.edgeCount (canonical_indices left) index hi
  · exact fun index hi => h.2.1.index_lt right.edgeCount (canonical_indices right) index hi

/-- Both original-index lists contain exactly one index per scored output edge. -/
theorem IndexedMaximum.indices_length {left right : OrderedTree} {leftWitness rightWitness : Word} {score : Nat}
    (h : IndexedMaximum left right leftWitness rightWitness score) :
    (indices leftWitness).length = score ∧ (indices rightWitness).length = score := by
  have hs : score = (erase leftWitness).semilength := h.2.2.2.2.trans (edgeCount_decodeDyck _)
  constructor
  · rw [SubtreeProofs.Paper2004.IndexedWord.indices_length,← erase_semilength,hs]
  · rw [SubtreeProofs.Paper2004.IndexedWord.indices_length,← erase_semilength,hs,h.2.2.1]

end SubtreeProofs.Paper2004.IndexedWord

end
