import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic

namespace SubtreeProofs.Lib.OrderedTree

/--
Core ordered rooted tree type used for reusable lemmas.

This intentionally fixes one canonical representation so different project-specific
variants can be connected via conversion layers.
-/
inductive Tree : Type
  | node : List Tree → Tree
deriving Repr

namespace Tree

/-- Number of nodes. -/
def nodes : Tree → Nat
  | node cs => 1 + (cs.map nodes).sum

/-- Number of edges. -/
def edges : Tree → Nat
  | node cs => cs.length + (cs.map edges).sum

/-- Depth with root depth `1`. -/
def depth1 : Tree → Nat
  | node [] => 1
  | node cs => 1 + (cs.map depth1).foldr Nat.max 0

/-- Depth with root depth `0` (derived from `depth1`). -/
def depth0 (t : Tree) : Nat := depth1 t - 1

/-- Number of leaves. -/
def leaves : Tree → Nat
  | node [] => 1
  | node cs => (cs.map leaves).sum

/-- Root-depth-1 convention is always positive. -/
theorem depth1_pos (t : Tree) : 1 ≤ depth1 t := by
  cases t with
  | node cs =>
      cases cs with
      | nil => simp [depth1]
      | cons c cs => simp [depth1]

/-- There is always at least one node. -/
theorem nodes_pos (t : Tree) : 1 ≤ nodes t := by
  cases t with
  | node cs => simp [nodes]

end Tree

end SubtreeProofs.Lib.OrderedTree
