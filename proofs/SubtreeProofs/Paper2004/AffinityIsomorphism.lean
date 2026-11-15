module

public import SubtreeProofs.Paper2004.AnnotatedIsomorphism
public import Mathlib.Algebra.Order.Ring.Basic
import Mathlib.Tactic

/-! # Independent original-identity and affinity isomorphism witnesses

A common forest carries a pair of original identities at each matched vertex.
Its projections must be whole-subtree prunings of the original inputs. This
simultaneously enforces common shape, adjacency and sibling order. Positive
affinity is required at every retained pair; zero forbids matching, as in the
author's extension. The objective is a separate additive forest fold.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.AnnotatedIso

def leftProjection {L R : Type*} (witness : Word (L × R)) : Word L := witness.map Prod.fst
def rightProjection {L R : Type*} (witness : Word (L × R)) : Word R := witness.map Prod.snd

theorem vertices_map {L R : Type*} (f : L → R) (word : Word L) :
    vertices (word.map f) = (vertices word).map f := by
  induction word with
  | nil => rfl
  | node label head tail ihHead ihTail => simp [BinaryTree.map,vertices,ihHead,ihTail]

@[simp] theorem numNodes_map {L R : Type*} (f : L → R) (word : Word L) :
    (word.map f).numNodes = word.numNodes := by
  induction word with
  | nil => rfl
  | node label head tail ihHead ihTail => simp [BinaryTree.map,BinaryTree.numNodes,ihHead,ihTail]

theorem erase_map {L R : Type*} (f : L → R) (word : Word L) : erase (word.map f) = erase word := by
  induction word with
  | nil => rfl
  | node label head tail ihHead ihTail => simp [BinaryTree.map,erase,ihHead,ihTail]

def score {L R K : Type*} [AddMonoid K] (affinity : L → R → K) : Word (L × R) → K
  | .nil => 0
  | .node pair head tail => score affinity head + score affinity tail + affinity pair.1 pair.2

def Compatible {L R K : Type*} [Zero K] [LT K] (affinity : L → R → K) (witness : Word (L × R)) : Prop :=
  ∀ pair ∈ vertices witness, 0 < affinity pair.1 pair.2

def LevelWitness {L R K : Type*} [Zero K] [LT K] (affinity : L → R → K)
    (witness : Word (L × R)) (left : Word L) (right : Word R) : Prop :=
  Prunes (leftProjection witness) left ∧ Prunes (rightProjection witness) right ∧ Compatible affinity witness

def AnyWitness {L R K : Type*} [Zero K] [LT K] (affinity : L → R → K)
    (witness : Word (L × R)) (left : Word L) (right : Word R) : Prop :=
  AnyPrunes (leftProjection witness) left ∧ AnyPrunes (rightProjection witness) right ∧ Compatible affinity witness

theorem compatible_node {L R K : Type*} [Zero K] [LT K] (affinity : L → R → K)
    (pair : L × R) (head tail : Word (L × R)) :
    Compatible affinity (.node pair head tail) ↔
      0 < affinity pair.1 pair.2 ∧ Compatible affinity head ∧ Compatible affinity tail := by
  simp [Compatible,vertices,or_imp,forall_and]

theorem Prunes.skip {L : Type*} {small tail : Word L} (h : Prunes small tail)
    (label : L) (head : Word L) : Prunes small (.node label head tail) := (Select.skip label head h.select).prunes

theorem Prunes.keep {L : Type*} {smallHead largeHead smallTail largeTail : Word L}
    (hHead : Prunes smallHead largeHead) (hTail : Prunes smallTail largeTail) (label : L) :
    Prunes (.node label smallHead smallTail) (.node label largeHead largeTail) :=
  (Select.keep hHead.select hTail.select).prunes

theorem level_empty {L R K : Type*} [Zero K] [LT K] (affinity : L → R → K) (left : Word L) (right : Word R) :
    LevelWitness affinity .nil left right :=
  ⟨Prunes.empty _,Prunes.empty _,by simp [Compatible,vertices]⟩

theorem LevelWitness.any {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : LevelWitness affinity witness left right) :
    AnyWitness affinity witness left right := ⟨h.1.any,h.2.1.any,h.2.2⟩

theorem level_node {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {head tail : Word (L × R)} {leftHead leftTail : Word L} {rightHead rightTail : Word R}
    (left : L) (right : R) (hHead : LevelWitness affinity head leftHead rightHead)
    (hTail : LevelWitness affinity tail leftTail rightTail) (hAffinity : 0 < affinity left right) :
    LevelWitness affinity (.node (left,right) head tail) (.node left leftHead leftTail) (.node right rightHead rightTail) :=
  ⟨hHead.1.keep hTail.1 left,hHead.2.1.keep hTail.2.1 right,
    (compatible_node affinity (left,right) head tail).mpr ⟨hAffinity,hHead.2.2,hTail.2.2⟩⟩

/-- Original preorder is preserved independently on both sides. -/
theorem LevelWitness.original_order {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : LevelWitness affinity witness left right) :
    ((vertices witness).map Prod.fst).Sublist (vertices left) ∧
      ((vertices witness).map Prod.snd).Sublist (vertices right) := by
  simpa only [leftProjection,rightProjection,vertices_map] using
    And.intro h.1.vertices_sublist h.2.1.vertices_sublist

theorem AnyWitness.original_order {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : AnyWitness affinity witness left right) :
    ((vertices witness).map Prod.fst).Sublist (vertices left) ∧
      ((vertices witness).map Prod.snd).Sublist (vertices right) := by
  simpa only [leftProjection,rightProjection,vertices_map] using
    And.intro h.1.vertices_sublist h.2.1.vertices_sublist

/-- Unique original identities give a partial bijection, rather than a
shape-only witness that may reuse one original input vertex. -/
theorem AnyWitness.unique_endpoints {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : AnyWitness affinity witness left right)
    (hLeft : (vertices left).Nodup) (hRight : (vertices right).Nodup) :
    ((vertices witness).map Prod.fst).Nodup ∧ ((vertices witness).map Prod.snd).Nodup :=
  ⟨h.original_order.1.nodup hLeft,h.original_order.2.nodup hRight⟩

theorem AnyWitness.parent_preserving {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : AnyWitness affinity witness left right) :
    (∀ edge ∈ parentEdges (leftProjection witness), edge ∈ parentEdges left) ∧
      (∀ edge ∈ parentEdges (rightProjection witness), edge ∈ parentEdges right) :=
  ⟨h.1.parentEdges_subset,h.2.1.parentEdges_subset⟩

theorem AnyWitness.numNodes_le {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : AnyWitness affinity witness left right) :
    witness.numNodes ≤ min left.numNodes right.numNodes := by
  have hl := h.1.numNodes_le
  have hr := h.2.1.numNodes_le
  simpa only [leftProjection,rightProjection,numNodes_map,le_min_iff] using And.intro hl hr

/-- Forgetting identities recovers the established unlabelled contract. -/
theorem LevelWitness.erase {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : LevelWitness affinity witness left right) :
    OrderedTree.RootPrunes (.node (erase witness)) (.node (erase left)) ∧
      OrderedTree.RootPrunes (.node (erase witness)) (.node (erase right)) := by
  constructor
  · apply OrderedTree.RootPrunes.node
    simpa only [leftProjection,erase_map] using h.1.select.erase
  · apply OrderedTree.RootPrunes.node
    simpa only [rightProjection,erase_map] using h.2.1.select.erase

theorem AnyWitness.erase {L R K : Type*} [Zero K] [LT K] {affinity : L → R → K}
    {witness : Word (L × R)} {left : Word L} {right : Word R} (h : AnyWitness affinity witness left right) :
    OrderedTree.IsomorphicSubtree (.node (erase witness)) (.node (erase left)) ∧
      OrderedTree.IsomorphicSubtree (.node (erase witness)) (.node (erase right)) := by
  simpa only [leftProjection,rightProjection,erase_map] using And.intro h.1.erase h.2.1.erase

variable {L R K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem Compatible.score_nonnegative {affinity : L → R → K} {witness : Word (L × R)}
    (h : Compatible affinity witness) : 0 ≤ score affinity witness := by
  induction witness with
  | nil => exact le_refl _
  | node pair head tail ihHead ihTail =>
    obtain ⟨hp,hh,ht⟩ := (compatible_node affinity pair head tail).mp h
    have hHead := ihHead hh
    have hTail := ihTail ht
    simp only [score]
    linarith

def IsMaximumLevel (affinity : L → R → K) (witness : Word (L × R)) (left : Word L) (right : Word R) : Prop :=
  LevelWitness affinity witness left right ∧
    ∀ other, LevelWitness affinity other left right → score affinity other ≤ score affinity witness

def IsMaximumAny (affinity : L → R → K) (witness : Word (L × R)) (left : Word L) (right : Word R) : Prop :=
  AnyWitness affinity witness left right ∧
    ∀ other, AnyWitness affinity other left right → score affinity other ≤ score affinity witness

end SubtreeProofs.Paper2004.AnnotatedIso

end
