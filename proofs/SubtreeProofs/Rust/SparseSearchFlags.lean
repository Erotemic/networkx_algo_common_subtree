module

public import SubtreeProofs.Rust.SparseCutStep
public import SubtreeProofs.Rust.SparseSearchInverse
public import SubtreeProofs.Shared.AssignmentSparseSearch
import Mathlib.Tactic

/-! # Actual Boolean-vector writes represent alternating-cut growth -/

@[expose] public section

open Aeneas Aeneas.Std
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

open SparseCut AssignmentScanInvariant

theorem chosen_set_true (cost : Slice (alloc.vec.Vec (Option I64))) (flags : alloc.vec.Vec Bool)
    (index : Usize) (hl : flags.length = cost.length) (hi : index.val < cost.length) :
    chosen cost (alloc.vec.Vec.deref (flags.set index true)) =
      insert (⟨index.val,hi⟩ : Vertex cost) (chosen cost (alloc.vec.Vec.deref flags)) := by
  ext vertex
  simp only [mem_chosen,Finset.mem_insert,alloc.vec.Vec.deref,Slice.from_val]
  by_cases he : vertex.val = index.val
  · have hv : vertex = (⟨index.val,hi⟩ : Vertex cost) := Fin.ext he
    rw [hv,vec_set_self flags index true (by omega)]
    simp
  · rw [vec_set_other flags index true vertex.val (by omega) (Ne.symm he)]
    have hv : vertex ≠ (⟨index.val,hi⟩ : Vertex cost) := fun hh => he (congrArg Fin.val hh)
    simp only [hv,false_or]

theorem chosen_false (cost : Slice (alloc.vec.Vec (Option I64))) (flags : alloc.vec.Vec Bool)
    (h : flags.val = List.replicate cost.length false) : chosen cost (alloc.vec.Vec.deref flags) = ∅ := by
  ext vertex
  simp only [mem_chosen,alloc.vec.Vec.deref,Slice.from_val,h,List.getElem!_replicate,vertex.isLt,↓reduceIte,
    Bool.false_eq_true,Finset.notMem_empty]

theorem chosen_initial_root (cost : Slice (alloc.vec.Vec (Option I64))) (flags : alloc.vec.Vec Bool)
    (root : Usize) (hr : root.val < cost.length) (h : flags.val = List.replicate cost.length false) :
    chosen cost (alloc.vec.Vec.deref (flags.set root true)) = {⟨root.val,hr⟩} := by
  rw [chosen_set_true cost flags root (by simp only [alloc.vec.Vec.length,h,List.length_replicate]) hr,chosen_false cost flags h]
  rfl

/-- The actual two flag writes of a nonterminal Rust iteration implement the
independent inverse-image cut extension in original zero-based coordinates. -/
theorem chosen_search_extension (cost : Slice (alloc.vec.Vec (Option I64)))
    (rows columns : alloc.vec.Vec Bool) (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost)
    (column row : Usize) (hcl : columns.length = cost.length) (hrl : rows.length = cost.length)
    (hc : column.val < cost.length) (hr : row.val < cost.length)
    (hi : row.val = (assignment.symm ⟨column.val,hc⟩).val)
    (hrows : chosen cost (alloc.vec.Vec.deref rows) = Assignment.searchRows assignment root (chosen cost (alloc.vec.Vec.deref columns))) :
    chosen cost (alloc.vec.Vec.deref (rows.set row true)) =
      Assignment.searchRows assignment root (chosen cost (alloc.vec.Vec.deref (columns.set column true))) := by
  rw [chosen_set_true cost rows row hrl hr,chosen_set_true cost columns column hcl hc,hrows,Assignment.searchRows_insert]
  have he : (⟨row.val,hr⟩ : Vertex cost) = assignment.symm ⟨column.val,hc⟩ := Fin.ext hi
  rw [he]

/-- A fresh nonterminal source flag update increases the selected-column
count exactly once and strictly decreases the mathematical search measure. -/
theorem chosen_extension_measure (cost : Slice (alloc.vec.Vec (Option I64))) (columns : alloc.vec.Vec Bool)
    (assignment : Equiv.Perm (Vertex cost)) (root : Vertex cost) (column : Usize)
    (hl : columns.length = cost.length) (hc : column.val < cost.length)
    (hfree : assignment root ∉ chosen cost (alloc.vec.Vec.deref columns))
    (hf : (⟨column.val,hc⟩ : Vertex cost) ∉ chosen cost (alloc.vec.Vec.deref columns)) :
    (chosen cost (alloc.vec.Vec.deref (columns.set column true))).card = (chosen cost (alloc.vec.Vec.deref columns)).card+1 ∧
    cost.length-(chosen cost (alloc.vec.Vec.deref (columns.set column true))).card <
      cost.length-(chosen cost (alloc.vec.Vec.deref columns)).card := by
  rw [chosen_set_true cost columns column hl hc]
  refine ⟨Finset.card_insert_of_notMem hf,?_⟩
  simpa only [Vertex,Fintype.card_fin] using Assignment.search_cut_measure_decreases assignment root ⟨column.val,hc⟩
    (chosen cost (alloc.vec.Vec.deref columns)) hfree hf

end SubtreeProofs.Rust.SparseSearch

end
