import SubtreeProofs.Paper2004.BalancedSequence

/-!
# Ordered rooted trees and Dyck words: a two-sided equivalence

A rooted ordered tree is represented by the binary tree of its ordered child
forest: the left branch is the first child's own child forest, and the right
branch contains its following siblings. The distinguished root contributes no
binary node, so binary node count agrees with the number of edges.

Mathlib proves that `DyckWord.toTree` and `DyckWord.ofTree` are inverse maps.
Here we prove the *additional* correspondence between that binary-tree encoding
and the independent `OrderedTree` type, and connect it to `encodeDyck`.

This does not assume any relation between contractions and Dyck-word deletion.
-/

namespace SubtreeProofs.Paper2004
namespace OrderedTree

mutual
  /-- First-child/next-sibling representation of a tree's child forest.
  The virtual top-level root is not represented by a binary node. -/
  def toBinaryTree : OrderedTree -> BinaryTree Unit
    | .node children => toBinaryForest children

  def toBinaryForest : List OrderedTree -> BinaryTree Unit
    | [] => .nil
    | child :: rest =>
        .node () (toBinaryTree child) (toBinaryForest rest)
end

/-- Recover the ordered forest from a first-child/next-sibling binary tree. -/
def fromBinaryForest : BinaryTree Unit -> List OrderedTree
  | .nil => []
  | .node _ firstChildForest followingSiblings =>
      .node (fromBinaryForest firstChildForest) ::
        fromBinaryForest followingSiblings

/-- Recover a rooted tree by attaching the decoded forest to a new root. -/
def fromBinaryTree (binary : BinaryTree Unit) : OrderedTree :=
  .node (fromBinaryForest binary)

/-- Encoding a decoded binary forest restores exactly that binary tree. -/
theorem toBinaryForest_fromBinaryForest (binary : BinaryTree Unit) :
    toBinaryForest (fromBinaryForest binary) = binary := by
  induction binary with
  | nil => rfl
  | node value first following ihFirst ihFollowing =>
      cases value
      change BinaryTree.node ()
          (toBinaryForest (fromBinaryForest first))
          (toBinaryForest (fromBinaryForest following)) =
        BinaryTree.node () first following
      rw [ihFirst, ihFollowing]

/-- Adding the implicit root and then encoding its forest is also an inverse. -/
theorem toBinaryTree_fromBinaryTree (binary : BinaryTree Unit) :
    toBinaryTree (fromBinaryTree binary) = binary := by
  change toBinaryForest (fromBinaryForest binary) = binary
  exact toBinaryForest_fromBinaryForest binary

mutual
  /-- The reverse round trip requires joint induction over trees and forests. -/
  theorem fromBinaryTree_toBinaryTree (tree : OrderedTree) :
      fromBinaryTree (toBinaryTree tree) = tree := by
    cases tree with
    | node children =>
        change OrderedTree.node (fromBinaryForest (toBinaryForest children)) =
          OrderedTree.node children
        rw [fromBinaryForest_toBinaryForest children]

  theorem fromBinaryForest_toBinaryForest (forest : List OrderedTree) :
      fromBinaryForest (toBinaryForest forest) = forest := by
    cases forest with
    | nil => rfl
    | cons child rest =>
        change OrderedTree.node (fromBinaryForest (toBinaryTree child)) ::
            fromBinaryForest (toBinaryForest rest) = child :: rest
        have hChild := fromBinaryTree_toBinaryTree child
        change OrderedTree.node (fromBinaryForest (toBinaryTree child)) =
          child at hChild
        rw [hChild, fromBinaryForest_toBinaryForest rest]
end

mutual
  /-- The pre-existing recursive Dyck encoding agrees with Mathlib's encoding of
  our first-child/next-sibling binary representation. -/
  theorem encodeDyck_eq_ofTree_toBinaryTree (tree : OrderedTree) :
      encodeDyck tree = DyckWord.ofTree (toBinaryTree tree) := by
    cases tree with
    | node children =>
        change encodeForestDyck children =
          DyckWord.ofTree (toBinaryForest children)
        exact encodeForestDyck_eq_ofTree_toBinaryForest children

  theorem encodeForestDyck_eq_ofTree_toBinaryForest
      (forest : List OrderedTree) :
      encodeForestDyck forest = DyckWord.ofTree (toBinaryForest forest) := by
    cases forest with
    | nil => rfl
    | cons child rest =>
        change (encodeDyck child).nest + encodeForestDyck rest =
          (DyckWord.ofTree (toBinaryTree child)).nest +
            DyckWord.ofTree (toBinaryForest rest)
        rw [encodeDyck_eq_ofTree_toBinaryTree child,
          encodeForestDyck_eq_ofTree_toBinaryForest rest]
end

/-- Decode an arbitrary Dyck word as a finite rooted ordered tree. -/
def decodeDyck (word : DyckWord) : OrderedTree :=
  fromBinaryTree word.toTree

/-- Decoding the encoding of an ordered tree recovers the original tree. -/
@[simp] theorem decodeDyck_encodeDyck (tree : OrderedTree) :
    decodeDyck (encodeDyck tree) = tree := by
  unfold decodeDyck
  rw [encodeDyck_eq_ofTree_toBinaryTree,
    DyckWord.toTree_ofTree, fromBinaryTree_toBinaryTree]

/-- Encoding the decoding of a Dyck word recovers the original word. -/
@[simp] theorem encodeDyck_decodeDyck (word : DyckWord) :
    encodeDyck (decodeDyck word) = word := by
  unfold decodeDyck
  rw [encodeDyck_eq_ofTree_toBinaryTree,
    toBinaryTree_fromBinaryTree, DyckWord.ofTree_toTree]

/-- Every Dyck word codes exactly one finite, rooted, ordered tree. -/
def orderedTreeEquivDyck : OrderedTree ≃ DyckWord where
  toFun := encodeDyck
  invFun := decodeDyck
  left_inv := decodeDyck_encodeDyck
  right_inv := encodeDyck_decodeDyck

/-- Distinct ordered trees have distinct Dyck encodings. -/
theorem encodeDyck_injective : Function.Injective encodeDyck := by
  intro first second h
  have hDecode := congrArg decodeDyck h
  simpa only [decodeDyck_encodeDyck] using hDecode

/-- The edge-count equation also holds when starting from an arbitrary word. -/
@[simp] theorem edgeCount_decodeDyck (word : DyckWord) :
    edgeCount (decodeDyck word) = word.semilength := by
  have h := encodeDyck_semilength (decodeDyck word)
  rw [encodeDyck_decodeDyck] at h
  exact h.symm

end OrderedTree
end SubtreeProofs.Paper2004
