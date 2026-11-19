module

public import SubtreeProofs.Shared.AssignmentDeletedPermutation
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic

/-! # Compact surviving coordinates preserve original assignment vertices -/

@[expose] public section

namespace SubtreeProofs.AssignmentVertexDeletion

/-- Increasing compact coordinates enumerate precisely the original vertices
other than the removed one. This is the standard `Fin.succAbove` embedding. -/
noncomputable def remainingEquiv {n : Nat} (removed : Fin (n+1)) :
    Fin n ≃ {vertex : Fin (n+1) // vertex ≠ removed} :=
  Equiv.ofBijective (fun vertex => ⟨removed.succAbove vertex,Fin.succAbove_ne removed vertex⟩) (by
    constructor
    · intro first second he
      exact Fin.succAbove_right_injective (congrArg Subtype.val he)
    · intro vertex
      obtain ⟨index,hIndex⟩ := Fin.exists_succAbove_eq vertex.property
      exact ⟨index,Subtype.ext hIndex⟩)

@[simp] theorem remainingEquiv_value {n : Nat} (removed : Fin (n+1)) (vertex : Fin n) :
    (remainingEquiv removed vertex).val = removed.succAbove vertex := rfl

/-- Exact original-index expansion used by the Rust projection loops. -/
theorem remainingEquiv_val {n : Nat} (removed : Fin (n+1)) (vertex : Fin n) :
    (remainingEquiv removed vertex).val.val = if vertex.val < removed.val then vertex.val else vertex.val+1 := by
  rw [remainingEquiv_value]
  unfold Fin.succAbove
  split
  · rename_i h
    have hv : vertex.val < removed.val := h
    simp only [Fin.val_castSucc,hv,↓reduceIte]
  · rename_i h
    have hv : ¬ vertex.val < removed.val := h
    simp only [Fin.val_succ,hv,↓reduceIte]

/-- The inverse removes exactly one skipped original coordinate. It never
collapses an actual surviving original vertex into the deleted one. -/
theorem remainingEquiv_symm_val {n : Nat} (removed : Fin (n+1)) (vertex : {v : Fin (n+1) // v ≠ removed}) :
    ((remainingEquiv removed).symm vertex).val = if vertex.val.val < removed.val then vertex.val.val else vertex.val.val-1 := by
  have he := remainingEquiv_val removed ((remainingEquiv removed).symm vertex)
  rw [Equiv.apply_symm_apply] at he
  split at he <;> split <;> omega

/-- The bypass-completed surviving permutation transported to compact source
coordinates. Its values still expand to the actual original bypass edges. -/
noncomputable def compactAssignment {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1)) : Equiv.Perm (Fin n) :=
  (remainingEquiv removed).trans ((onRemaining assignment removed).trans (remainingEquiv removed).symm)

theorem compactAssignment_value {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1)) (row : Fin n) :
    (remainingEquiv removed (compactAssignment assignment removed row)).val = bypass assignment removed (removed.succAbove row) := by
  simp only [compactAssignment,Equiv.trans_apply,Equiv.apply_symm_apply,onRemaining_value,remainingEquiv_value]

noncomputable def compactFree {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed ≠ removed) : Fin n :=
  (remainingEquiv removed).symm (freeRow assignment removed hn)

@[simp] theorem compactFree_value {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed ≠ removed) :
    (remainingEquiv removed (compactFree assignment removed hn)).val = assignment.symm removed := by
  rw [compactFree,Equiv.apply_symm_apply]
  rfl

/-- Every compact row other than the unique free root keeps its actual old
assignment edge, expressed in original surviving vertex coordinates. -/
theorem compactAssignment_away {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed ≠ removed) (row : Fin n) (hr : row ≠ compactFree assignment removed hn) :
    removed.succAbove (compactAssignment assignment removed row) = assignment (removed.succAbove row) := by
  have hf : removed.succAbove row ≠ assignment.symm removed := by
    intro he
    apply hr
    apply (remainingEquiv removed).injective
    apply Subtype.ext
    change removed.succAbove row = (remainingEquiv removed (compactFree assignment removed hn)).val
    rw [compactFree_value]
    exact he
  have hh := compactAssignment_value assignment removed row
  rw [bypass_away assignment removed (removed.succAbove row) (Fin.succAbove_ne removed row) hf] at hh
  exact hh

/-- The compact temporary completion joins exactly the surviving old free
row and old free column, rather than a newly chosen or renumbered endpoint. -/
theorem compactAssignment_free {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed ≠ removed) :
    removed.succAbove (compactAssignment assignment removed (compactFree assignment removed hn)) = assignment removed := by
  have hh := compactAssignment_value assignment removed (compactFree assignment removed hn)
  have hf : removed.succAbove (compactFree assignment removed hn) = assignment.symm removed := compactFree_value assignment removed hn
  rw [hf,bypass_free assignment removed] at hh
  exact hh

/-- A paired deletion requires no augmentation: every compact edge is simply
the corresponding surviving old edge. -/
theorem compactAssignment_paired {n : Nat} (assignment : Equiv.Perm (Fin (n+1))) (removed : Fin (n+1))
    (hn : assignment removed = removed) (row : Fin n) :
    removed.succAbove (compactAssignment assignment removed row) = assignment (removed.succAbove row) := by
  have hi : assignment.symm removed = removed := (Equiv.symm_apply_eq assignment).mpr hn.symm
  have hh := compactAssignment_value assignment removed row
  rw [bypass_away assignment removed (removed.succAbove row) (Fin.succAbove_ne removed row) (by rw [hi]; exact Fin.succAbove_ne removed row)] at hh
  exact hh

end SubtreeProofs.AssignmentVertexDeletion

end
