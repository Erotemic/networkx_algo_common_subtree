import Mathlib.Logic.Relation
import Mathlib.Tactic

/-!
# Ordered rooted trees and edge contraction

An independent specification of the unlabeled, rooted, ordered problem.
The root is preserved. Contracting a parent-child edge removes the child
vertex, splicing its own children into the parent's child list at the same
position. The `below` constructor permits contractions at arbitrary depth.

No balanced-sequence encoding, dynamic program or Rust representation occurs
in the definitions of the embedding relation or the optimization objective.
-/

namespace SubtreeProofs.Paper2004

/-- A nonempty rooted ordered tree; the children of each vertex are ordered. -/
inductive OrderedTree where
  | node : List OrderedTree → OrderedTree
  deriving Repr, Inhabited

namespace OrderedTree

/-- Ordered children of the root. -/
def children : OrderedTree → List OrderedTree
  | .node ts => ts

/-- A one-vertex tree, with no edges. -/
def singleton : OrderedTree := .node []

/-- A two-vertex path. -/
def oneEdge : OrderedTree := .node [singleton]

/-- A three-vertex tree with two leaf children. -/
def fork : OrderedTree := .node [singleton, singleton]

mutual
  /-- Edge count, with one edge for each child of a node. -/
  def edgeCount : OrderedTree → Nat
    | .node ts => forestEdgeCount ts

  def forestEdgeCount : List OrderedTree → Nat
    | [] => 0
    | t :: ts => (edgeCount t + 1) + forestEdgeCount ts
end

/-- Vertex count is edge count plus one for a nonempty tree. -/
def vertexCount (t : OrderedTree) : Nat := t.edgeCount + 1

mutual
  /-- Actual leaves: a vertex is a leaf precisely when it has no children. -/
  def leafCount : OrderedTree → Nat
    | .node [] => 1
    | .node (t :: ts) => forestLeafCount (t :: ts)

  def forestLeafCount : List OrderedTree → Nat
    | [] => 0
    | t :: ts => leafCount t + forestLeafCount ts
end

@[simp] theorem edgeCount_node (ts : List OrderedTree) :
    edgeCount (.node ts) = forestEdgeCount ts := rfl

@[simp] theorem forestEdgeCount_nil : forestEdgeCount [] = 0 := rfl

@[simp] theorem forestEdgeCount_cons (t : OrderedTree) (ts : List OrderedTree) :
    forestEdgeCount (t :: ts) = edgeCount t + 1 + forestEdgeCount ts := rfl

@[simp] theorem forestEdgeCount_append (as bs : List OrderedTree) :
    forestEdgeCount (as ++ bs) = forestEdgeCount as + forestEdgeCount bs := by
  induction as with
  | nil => simp
  | cons t ts ih => simp [ih, Nat.add_assoc]

@[simp] theorem edgeCount_singleton : edgeCount singleton = 0 := rfl
@[simp] theorem edgeCount_oneEdge : edgeCount oneEdge = 1 := rfl
@[simp] theorem leafCount_singleton : leafCount singleton = 1 := rfl
@[simp] theorem leafCount_oneEdge : leafCount oneEdge = 1 := rfl
@[simp] theorem leafCount_fork : leafCount fork = 2 := rfl

/-- An ordered tree with one hole.  Replacing the hole by a tree preserves
all the surrounding ancestors and the ordering of their children. -/
inductive Context where
  | hole : Context
  | under (left right : List OrderedTree) (inner : Context) : Context

namespace Context

/-- Fill a single hole in an ordered tree context. -/
def plug : Context -> OrderedTree -> OrderedTree
  | .hole, t => t
  | .under left right inner, t =>
      .node (left ++ [plug inner t] ++ right)

/-- Edges contributed by a context, including the edge leading to its hole. -/
def edgeOverhead : Context -> Nat
  | .hole => 0
  | .under left right inner =>
      forestEdgeCount left + 1 + forestEdgeCount right + edgeOverhead inner

/-- Substituting a tree into a context adds a fixed number of edges. -/
theorem edgeCount_plug (ctx : Context) (t : OrderedTree) :
    edgeCount (ctx.plug t) = edgeCount t + ctx.edgeOverhead := by
  induction ctx with
  | hole => simp [plug, edgeOverhead]
  | under left right inner ih =>
      simp only [plug, edgeCount_node, forestEdgeCount_append,
        forestEdgeCount_cons, forestEdgeCount_nil, edgeOverhead, ih]
      omega

end Context

/-- A single edge contraction at any depth. The witness specifies the enclosing
context, the sibling lists, and the child whose incoming edge is contracted. -/
def ContractStep (before after : OrderedTree) : Prop :=
  Exists fun (ctx : Context) =>
  Exists fun (left : List OrderedTree) =>
  Exists fun (right : List OrderedTree) =>
  Exists fun (child : OrderedTree) =>
    before = ctx.plug (.node (left ++ [child] ++ right)) /\
    after = ctx.plug (.node (left ++ children child ++ right))

/-- Contract an edge incident to the root. -/
theorem ContractStep.atRoot (left right : List OrderedTree) (child : OrderedTree) :
    ContractStep
      (.node (left ++ [child] ++ right))
      (.node (left ++ children child ++ right)) := by
  exact ⟨Context.hole, left, right, child, rfl, rfl⟩

/-- Lift any contraction into a child without disturbing its siblings. -/
theorem ContractStep.below (left right : List OrderedTree) {before after : OrderedTree}
    (step : ContractStep before after) :
    ContractStep
      (.node (left ++ [before] ++ right))
      (.node (left ++ [after] ++ right)) := by
  rcases step with ⟨ctx, innerLeft, innerRight, child, hb, ha⟩
  refine ⟨Context.under left right ctx, innerLeft, innerRight, child, ?_, ?_⟩
  · simpa only [Context.plug, hb]
  · simpa only [Context.plug, ha]

/-- Every single edge contraction removes exactly one edge. -/
theorem ContractStep.edgeCount_decreases {before after : OrderedTree}
    (h : ContractStep before after) :
    edgeCount before = edgeCount after + 1 := by
  rcases h with ⟨ctx, left, right, child, hb, ha⟩
  have hroot :
      edgeCount (.node (left ++ [child] ++ right)) =
        edgeCount (.node (left ++ children child ++ right)) + 1 := by
    cases child with
    | node grandchildren =>
        simp only [children, edgeCount_node, forestEdgeCount_append,
          forestEdgeCount_cons, forestEdgeCount_nil]
        omega
  have hbefore := Context.edgeCount_plug ctx (.node (left ++ [child] ++ right))
  have hafter := Context.edgeCount_plug ctx (.node (left ++ children child ++ right))
  rw [hb, ha]
  omega

/-- `small` is obtainable from `large` by zero or more edge contractions.
This relation is specified solely in terms of trees. -/
def Embeds (small large : OrderedTree) : Prop :=
  Relation.ReflTransGen ContractStep large small

theorem embeds_refl (t : OrderedTree) : Embeds t t := by
  exact Relation.ReflTransGen.refl

theorem embeds_of_step {large small : OrderedTree}
    (h : ContractStep large small) : Embeds small large :=
  Relation.ReflTransGen.single h

theorem embeds_trans {a b c : OrderedTree}
    (hab : Embeds a b) (hbc : Embeds b c) : Embeds a c :=
  Relation.ReflTransGen.trans hbc hab

/-- A contracted subtree cannot have more edges than the original. -/
theorem embeds_edgeCount_le {small large : OrderedTree}
    (h : Embeds small large) : edgeCount small ≤ edgeCount large := by
  unfold Embeds at h
  induction h with
  | refl => exact Nat.le_refl _
  | tail hprefix hstep ih =>
      have hcount := ContractStep.edgeCount_decreases hstep
      omega

/-- A tree embedded into both inputs. -/
def CommonEmbedding (candidate left right : OrderedTree) : Prop :=
  Embeds candidate left ∧ Embeds candidate right

/-- Independent maximum-common-embedded-subtree specification.
The score is the number of edges. The witness is the candidate tree itself. -/
def IsMaximumCommon (candidate left right : OrderedTree) : Prop :=
  CommonEmbedding candidate left right ∧
    ∀ other, CommonEmbedding other left right →
      edgeCount other ≤ edgeCount candidate

/-- Each tree is a maximum common embedding of itself with itself. -/
theorem isMaximumCommon_self (t : OrderedTree) : IsMaximumCommon t t t := by
  constructor
  · exact ⟨embeds_refl t, embeds_refl t⟩
  · intro other h
    exact embeds_edgeCount_le h.1

/-- The root edge of a one-edge path contracts to the singleton tree. -/
theorem singleton_embeds_oneEdge : Embeds singleton oneEdge := by
  apply embeds_of_step
  simpa [oneEdge, singleton, children] using
    (ContractStep.atRoot [] [] singleton)

/-- A contraction can occur strictly below the root. -/
theorem nested_contraction_example :
    Embeds (.node [singleton]) (.node [oneEdge]) := by
  apply embeds_of_step
  simpa [oneEdge, singleton, children] using
    (ContractStep.below [] []
      (ContractStep.atRoot [] [] singleton))

end OrderedTree
end SubtreeProofs.Paper2004
