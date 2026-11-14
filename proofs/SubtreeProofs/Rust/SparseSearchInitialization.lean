module

public import SubtreeProofs.Rust.SparseSearchLoop
import Mathlib.Tactic

/-! # Exact initial sparse-search invariant from actual zero-filled vectors -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut

theorem initial_invariant (cost : Slice (alloc.vec.Vec (Option I64)))
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (rootIndex : Usize) (hr : rootIndex.val = root.val)
    (initialRows initialColumns : Vertex cost → ℤ) (increment : ℤ) (rows columns : alloc.vec.Vec I128)
    (hrl : rows.length = cost.length) (hcl : columns.length = cost.length)
    (flags : alloc.vec.Vec Bool) (parents : alloc.vec.Vec Usize)
    (hf : flags.val = List.replicate cost.length false) (hp : parents.val = List.replicate cost.length 0#usize)
    (hFeasible : Assignment.FeasibleOn (allowed cost) (matrix cost) (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)))
    (hTight : ∀ row, row ≠ root → potentialAt cost (alloc.vec.Vec.deref rows) row+
      potentialAt cost (alloc.vec.Vec.deref columns) (assignment row) = matrix cost row (assignment row))
    (hEnvelope : Assignment.BiEnvelope initialRows initialColumns (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) increment)
    (hAccount : Assignment.dualValue (potentialAt cost (alloc.vec.Vec.deref rows)) (potentialAt cost (alloc.vec.Vec.deref columns)) =
      Assignment.dualValue initialRows initialColumns+increment) :
    Invariant cost assignment root initialRows initialColumns increment rows columns (flags.set rootIndex true) flags parents parents 0#usize true none := by
  have hFlagsLen : flags.length = cost.length := by simp only [alloc.vec.Vec.length,hf,List.length_replicate]
  have hParentsLen : parents.length = cost.length := by simp only [alloc.vec.Vec.length,hp,List.length_replicate]
  have hRoot : rootIndex.val < cost.length := by rw [hr]; exact root.isLt
  have hRootEq : (⟨rootIndex.val,hRoot⟩ : Vertex cost) = root := Fin.ext hr
  have hEmpty := chosen_false cost flags hf
  have hSingle : chosen cost (alloc.vec.Vec.deref (flags.set rootIndex true)) = {root} := by
    rw [chosen_initial_root cost flags rootIndex hRoot hf,hRootEq]
  refine {
    rows_length := hrl
    columns_length := hcl
    selected_rows_length := by simpa using hFlagsLen
    selected_columns_length := hFlagsLen
    predecessor_length := hParentsLen
    discovery_length := hParentsLen
    failure_none := rfl
    rows_exact := ?_
    free_outside := by rw [hEmpty]; exact Finset.notMem_empty _
    steps_card := by simp only [hEmpty,Finset.card_empty,UScalar.ofNatCore_val_eq,↓reduceIte,Nat.add_zero]
    feasible := hFeasible
    matching_tight := hTight
    envelope := hEnvelope
    account := hAccount
    discovery_exact := ?_
    discovery_bound := ?_
    predecessor_edges := ?_
  }
  · rw [hSingle,hEmpty]
    simp only [Assignment.searchRows,Finset.image_empty]
    rfl
  · intro column
    simp only [hp,List.getElem!_replicate,column.isLt,↓reduceIte,UScalar.ofNatCore_val_eq,lt_self_iff_false,
      discovered,hEmpty,Finset.union_empty,Finset.notMem_empty]
  · intro column
    simp only [hp,List.getElem!_replicate,column.isLt,↓reduceIte,UScalar.ofNatCore_val_eq,le_refl]
  · intro column hc
    simp only [discovered,hEmpty,↓reduceIte,Finset.union_empty,Finset.notMem_empty] at hc

end SubtreeProofs.Rust.SparseSearch

end
