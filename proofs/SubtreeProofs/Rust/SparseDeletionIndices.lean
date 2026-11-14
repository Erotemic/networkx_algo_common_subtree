module

public import SubtreeProofs.Rust.AssignmentInitialization
public import SubtreeProofs.Shared.AssignmentFiniteDeletion
import Mathlib.Tactic

/-! # Actual sparse deletion coordinate compression -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseDeletion

/-- Every represented source compression either rejects the removed vertex
or returns the exact coordinate obtained by skipping it. -/
theorem compact_index_total_spec (vertex removed : Usize) :
    sparse_deletion.compact_index vertex removed ⦃ result =>
      if vertex = removed then result = core.result.Result.Err AssignmentError.InvariantViolation
      else ∃ compact, result = core.result.Result.Ok compact ∧
        compact.val = if vertex.val < removed.val then vertex.val else vertex.val-1 ⦄ := by
  unfold sparse_deletion.compact_index
  split
  · rename_i he
    exact (WP.spec_ok _).mpr (by simp only [he,↓reduceIte])
  · rename_i he
    split
    · rename_i hlt
      exact (WP.spec_ok _).mpr ⟨vertex,rfl,by rw [ite_eq_left (show vertex.val < removed.val from hlt)]⟩
    · rename_i hnot
      have hPositive : 0 < vertex.val := by
        have hNe : vertex.val ≠ removed.val := fun hh => he (UScalar.eq_of_val_eq hh)
        have hLe : removed.val ≤ vertex.val := le_of_not_gt hnot
        omega
      apply WP.spec_bind (Usize.sub_spec (x := vertex) (y := 1#usize) (by scalar_tac))
      intro compact hCompact
      apply (WP.spec_ok _).mpr
      refine ⟨compact,rfl,?_⟩
      rw [ite_eq_right (show ¬ vertex.val < removed.val from hnot)]
      simpa only [UScalar.ofNatCore_val_eq] using hCompact.1

/-- On an actual surviving original finite vertex the source returns exactly
the inverse of the canonical increasing surviving-coordinate equivalence. -/
theorem compact_index_remaining_spec {n : Nat} (removed : Fin (n+1))
    (vertex : {v : Fin (n+1) // v ≠ removed}) (rawVertex rawRemoved : Usize)
    (hv : rawVertex.val = vertex.val.val) (hr : rawRemoved.val = removed.val) :
    sparse_deletion.compact_index rawVertex rawRemoved ⦃ result => ∃ compact,
      result = core.result.Result.Ok compact ∧ compact.val = ((AssignmentVertexDeletion.remainingEquiv removed).symm vertex).val ⦄ := by
  have hNe : rawVertex ≠ rawRemoved := by
    intro he
    have hh := congrArg UScalar.val he
    rw [hv,hr] at hh
    exact vertex.property (Fin.ext hh)
  apply WP.spec_mono (compact_index_total_spec rawVertex rawRemoved)
  intro result hResult
  rw [ite_eq_right hNe] at hResult
  obtain ⟨compact,hResult,hValue⟩ := hResult
  refine ⟨compact,hResult,?_⟩
  rw [AssignmentVertexDeletion.remainingEquiv_symm_val,hValue,hv,hr]

end SubtreeProofs.Rust.SparseDeletion

end
