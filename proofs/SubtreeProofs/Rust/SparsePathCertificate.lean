module

public import SubtreeProofs.Rust.SparseSearchEntrypoint
public import SubtreeProofs.Shared.AssignmentRankedAugmentation
import Mathlib.Tactic

/-! # Actual search certificates induce independent ranked optimal augmentations -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut

/-- Interpret an original-index predecessor coordinate as a graph vertex.
The default root is irrelevant at positive-rank columns: the actual search
certificate proves those stored indices are in bounds and read back exactly. -/
def predecessorAt (cost : Slice (alloc.vec.Vec (Option I64))) (predecessor : alloc.vec.Vec Usize)
    (root column : Vertex cost) : Vertex cost :=
  if h : predecessor.val[column.val]!.val < cost.length then ⟨predecessor.val[column.val]!.val,h⟩ else root

def rankAt (cost : Slice (alloc.vec.Vec (Option I64))) (discovery : alloc.vec.Vec Usize) (column : Vertex cost) : Nat :=
  discovery.val[column.val]!.val

/-- Every positive-rank predecessor is an exact original source coordinate,
a real tight edge, and either the root or a link to an earlier positive rank. -/
theorem PathCertificate.predecessor_properties (cost : Slice (alloc.vec.Vec (Option I64)))
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (initialRows initialColumns : Vertex cost → ℤ)
    (result : sparse_search.SparseSearch) (h : PathCertificate cost assignment root initialRows initialColumns result)
    (column : Vertex cost) (hp : 0 < rankAt cost result.discovery column) :
    let row := predecessorAt cost result.predecessor_row root column
    result.predecessor_row.val[column.val]!.val = row.val ∧ allowed cost row column ∧
      potentialAt cost (alloc.vec.Vec.deref result.rows) row+potentialAt cost (alloc.vec.Vec.deref result.columns) column = matrix cost row column ∧
      (row = root ∨ 0 < rankAt cost result.discovery (assignment row) ∧
        rankAt cost result.discovery (assignment row) < rankAt cost result.discovery column) := by
  obtain ⟨row,hIndex,hAllowed,hTight,hRank⟩ := h.predecessor_edges column hp
  have hb : result.predecessor_row.val[column.val]!.val < cost.length := by rw [hIndex]; exact row.isLt
  have he : predecessorAt cost result.predecessor_row root column = row := by
    unfold predecessorAt
    rw [dite_eq_left hb]
    exact Fin.ext hIndex
  dsimp only
  rw [he]
  exact ⟨hIndex,hAllowed,hTight,hRank⟩

/-- The actual returned search data suffice to construct the globally optimal
one-path augmentation. Compatibility of unchanged old nonroot edges is the
natural matching-seed premise. This theorem interprets the certificate; the
separate source flip loop still has to be refined to this exact permutation. -/
theorem PathCertificate.exists_optimal_augmentation (cost : Slice (alloc.vec.Vec (Option I64)))
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (initialRows initialColumns : Vertex cost → ℤ)
    (result : sparse_search.SparseSearch) (h : PathCertificate cost assignment root initialRows initialColumns result)
    (hOldAllowed : ∀ row, row ≠ root → allowed cost row (assignment row)) :
    ∃ rest,
      Assignment.PredecessorTrace assignment (predecessorAt cost result.predecessor_row root) root (assignment root) (assignment root::rest) ∧
      (assignment root::rest).Nodup ∧
      Assignment.IsMinimumOn (allowed cost) (matrix cost) (Assignment.augmentTrace assignment (assignment root::rest)) ∧
      ∀ row, Assignment.augmentTrace assignment (assignment root::rest) row ∉ assignment root::rest →
        Assignment.augmentTrace assignment (assignment root::rest) row = assignment row := by
  exact Assignment.exists_ranked_augmentation (allowed cost) (matrix cost)
    (potentialAt cost (alloc.vec.Vec.deref result.rows)) (potentialAt cost (alloc.vec.Vec.deref result.columns))
    assignment (predecessorAt cost result.predecessor_row root) root (rankAt cost result.discovery)
    h.feasible hOldAllowed h.matching_tight h.target_discovered
    (fun column hp => (h.predecessor_properties cost assignment root initialRows initialColumns result column hp).2.2.2)
    (fun column hp => ⟨(h.predecessor_properties cost assignment root initialRows initialColumns result column hp).2.1,
      (h.predecessor_properties cost assignment root initialRows initialColumns result column hp).2.2.1⟩)

end SubtreeProofs.Rust.SparseSearch

end
