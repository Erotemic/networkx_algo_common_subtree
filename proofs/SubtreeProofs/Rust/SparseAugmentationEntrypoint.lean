module

public import SubtreeProofs.Rust.SparsePathFlipEntrypoint
import Mathlib.Tactic

/-! # Actual one-path sparse augmentation returns an independent optimum -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentNumericBounds

def CorrectAugmentation (cost : Slice (alloc.vec.Vec (Option I64))) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (initialRows initialColumns : Vertex cost → ℤ) (result : sparse_search.SparseAugmentation) : Prop :=
  PathCertificate cost assignment root initialRows initialColumns result.search ∧
  ∃ rest,
    Assignment.PredecessorTrace assignment (predecessorAt cost result.search.predecessor_row root) root (assignment root) (assignment root::rest) ∧
    (assignment root::rest).Nodup ∧ result.column_for_row.length = cost.length ∧
    (∀ row : Vertex cost, result.column_for_row.val[row.val]!.val = (Assignment.augmentTrace assignment (assignment root::rest) row).val) ∧
    Assignment.IsMinimumOn (allowed cost) (matrix cost) (Assignment.augmentTrace assignment (assignment root::rest)) ∧
    Assignment.Tight (matrix cost) (potentialAt cost (alloc.vec.Vec.deref result.search.rows))
      (potentialAt cost (alloc.vec.Vec.deref result.search.columns)) (Assignment.augmentTrace assignment (assignment root::rest)) ∧
    ∀ row, Assignment.augmentTrace assignment (assignment root::rest) row ∉ assignment root::rest →
      Assignment.augmentTrace assignment (assignment root::rest) row = assignment row

/-- Actual Rust search followed by actual checked path flipping returns a
globally minimum compatible permutation from a feasible tight single-deficit
matching. All original coordinate readback, path construction, ranks, bounds,
termination and machine checks are derived; no optimum or success certificate
is a premise. This reference search does not claim the paper's queue runtime. -/
theorem augment_sparse_permutation_spec (cost : Slice (alloc.vec.Vec (Option I64)))
    (rows columns : alloc.vec.Vec I128) (completed : Slice Usize) (rootIndex : Usize)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (hr : rootIndex.val = root.val)
    (hrl : rows.length = cost.length) (hcl : columns.length = cost.length) (hpl : completed.length = cost.length)
    (hPermutation : ∀ row : Vertex cost, completed.val[row.val]!.val = (assignment row).val)
    (hs : Square cost) (hn : cost.length ≤ U32.max)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ)
    (hInitialRows : ∀ row, -costMagnitude ≤ initialRows row ∧ initialRows row ≤ 0)
    (hInitialColumns : ∀ column, -costMagnitude ≤ initialColumns column ∧ initialColumns column ≤ 0)
    (hEnvelope : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) increment)
    (hAccount : Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) =
      Assignment.dualValue initialRows initialColumns+increment)
    (hFeasible : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)))
    (hOldAllowed : ∀ row, row ≠ root → allowed cost row (assignment row))
    (hTight : ∀ row, row ≠ root → potentialAt cost (alloc.vec.Vec.deref rows) row+
      potentialAt cost (alloc.vec.Vec.deref columns) (assignment row) = matrix cost row (assignment row))
    (hUpper : ∀ row column, allowed cost row column → matrix cost row column ≤ 0)
    (hCompatible : ∃ replacement : Equiv.Perm (Vertex cost), Assignment.Compatible (allowed cost) replacement) :
    sparse_search.augment_sparse_permutation cost rows columns completed rootIndex ⦃ result => ∃ output,
      result = core.result.Result.Ok output ∧ CorrectAugmentation cost assignment root initialRows initialColumns output ⦄ := by
  unfold sparse_search.augment_sparse_permutation
  apply WP.spec_bind (find_sparse_augmenting_path_spec cost rows columns completed rootIndex assignment root hr hrl hcl hpl hPermutation hs hn
    initialRows initialColumns increment hInitialRows hInitialColumns hEnvelope hAccount hFeasible hTight hUpper hCompatible)
  rintro result ⟨search,rfl,hSearch⟩
  let parent := predecessorAt cost search.predecessor_row root
  let rank := rankAt cost search.discovery
  have hFlipInput : FlipInput cost.length completed (alloc.vec.Vec.deref search.predecessor_row) (alloc.vec.Vec.deref search.discovery)
      (Slice.len completed) rootIndex assignment root parent rank := by
    refine ⟨(Slice.len_val completed).trans hpl,hpl,?_,?_,hr,hPermutation,?_,?_,?_⟩
    · simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using hSearch.predecessor_length
    · simpa only [alloc.vec.Vec.deref,Slice.from_val,Slice.length] using hSearch.discovery_length
    · intro column hp
      simpa only [alloc.vec.Vec.deref,Slice.from_val,parent] using
        (hSearch.predecessor_properties cost assignment root initialRows initialColumns search column hp).1
    · intro column
      simp only [alloc.vec.Vec.deref,Slice.from_val,rank,rankAt]
    · intro column hp
      exact (hSearch.predecessor_properties cost assignment root initialRows initialColumns search column hp).2.2.2
  apply WP.spec_bind (flip_sparse_path_spec cost.length completed (alloc.vec.Vec.deref search.predecessor_row) (alloc.vec.Vec.deref search.discovery)
    (Slice.len completed) rootIndex search.target assignment root parent rank hFlipInput hn hSearch.target_eq hSearch.target_discovered)
  rintro result ⟨rest,output,rfl,hTrace,hNodup,hPositive,hLength,hValues⟩
  have hNew : ∀ column ∈ assignment root::rest, allowed cost (parent column) column ∧
      potentialAt cost (alloc.vec.Vec.deref search.rows) (parent column)+potentialAt cost (alloc.vec.Vec.deref search.columns) column = matrix cost (parent column) column := by
    intro column hc
    have hp := hSearch.predecessor_properties cost assignment root initialRows initialColumns search column (hPositive column hc)
    exact ⟨hp.2.1,hp.2.2.1⟩
  obtain ⟨hAllowed,hFinalTight⟩ := Assignment.augmentTrace_compatible_tight (allowed cost) (matrix cost)
    (potentialAt cost (alloc.vec.Vec.deref search.rows)) (potentialAt cost (alloc.vec.Vec.deref search.columns))
    assignment parent root rest hTrace hNodup hOldAllowed hSearch.matching_tight hNew
  apply (WP.spec_ok _).mpr
  refine ⟨⟨output,search⟩,rfl,hSearch,rest,hTrace,hNodup,hLength,hValues,
    Assignment.isMinimumOn_of_feasible_tight hSearch.feasible hAllowed hFinalTight,hFinalTight,?_⟩
  intro row hm
  exact Assignment.augmentTrace_away assignment (assignment root::rest) row hm

end SubtreeProofs.Rust.SparseSearch

end
