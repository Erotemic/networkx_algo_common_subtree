import SubtreeProofs.Paper2004.OrderedTree
import Mathlib.Combinatorics.Enumerative.DyckWord

/-!
# Encoding ordered trees as balanced sequences

Each non-root vertex contributes one matching pair of Dyck steps. A child
subtree is surrounded by a pair; consecutive child subtrees concatenate.
The singleton tree therefore encodes as the empty Dyck word.

This module is downstream of the independent tree specification: no theorem
about sequence containment is used to define edge contraction.
-/

namespace SubtreeProofs.Paper2004
namespace OrderedTree

mutual
  /-- Balanced-sequence encoding of an entire rooted tree and its child forest. -/
  def encodeDyck : OrderedTree → DyckWord
    | .node ts => encodeForestDyck ts

  def encodeForestDyck : List OrderedTree → DyckWord
    | [] => 0
    | t :: ts => (encodeDyck t).nest + encodeForestDyck ts
end

mutual
  /-- The balanced-sequence semilength is exactly the number of tree edges. -/
  theorem encodeDyck_semilength (t : OrderedTree) :
      (encodeDyck t).semilength = edgeCount t := by
    cases t with
    | node ts =>
        simpa [encodeDyck, edgeCount] using encodeForestDyck_semilength ts

  theorem encodeForestDyck_semilength (ts : List OrderedTree) :
      (encodeForestDyck ts).semilength = forestEdgeCount ts := by
    cases ts with
    | nil => simp [encodeForestDyck, forestEdgeCount]
    | cons t rest =>
        simp [encodeForestDyck, forestEdgeCount,
          encodeDyck_semilength t, encodeForestDyck_semilength rest,
          Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
end

@[simp] theorem encodeDyck_singleton : encodeDyck singleton = 0 := rfl

theorem encodeDyck_oneEdge_semilength :
    (encodeDyck oneEdge).semilength = 1 := by
  rw [encodeDyck_semilength]
  rfl

end OrderedTree
end SubtreeProofs.Paper2004
