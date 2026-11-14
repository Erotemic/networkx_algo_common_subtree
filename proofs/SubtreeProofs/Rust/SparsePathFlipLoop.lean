module

public import SubtreeProofs.Rust.SparsePathFlipPreservation
import Mathlib.Tactic

/-! # The actual finite path-flip loop returns the canonical permutation -/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.SparseSearch

theorem flip_sparse_path_loop_spec (dimension : Nat) (completed predecessor discovery : Slice Usize) (n rootIndex : Usize)
    (assignment : Equiv.Perm (Fin dimension)) (root : Fin dimension) (parent : Fin dimension → Fin dimension) (rank : Fin dimension → Nat)
    (input : FlipInput dimension completed predecessor discovery n rootIndex assignment root parent rank)
    (rest : List (Fin dimension)) (current : alloc.vec.Vec Usize) (column cursor : Usize) (finished : Bool) (failure : Option AssignmentError)
    (h : FlipInvariant dimension assignment parent (assignment root::rest) current column cursor finished failure)
    (ht : Assignment.PredecessorTrace assignment parent root (assignment root) (assignment root::rest))
    (hn : (assignment root::rest).Nodup) (hPositive : ∀ col ∈ assignment root::rest, 0 < rank col) :
    sparse_search.flip_sparse_path_loop completed predecessor discovery rootIndex n current column cursor finished failure ⦃ output =>
      output.2 = none ∧ output.1.length = dimension ∧ ∀ row : Fin dimension,
        output.1.val[row.val]!.val = (Assignment.augmentTrace assignment (assignment root::rest) row).val ⦄ := by
  unfold sparse_search.flip_sparse_path_loop
  apply loop.spec_decr_nat (fun state : FlipState => (assignment root::rest).length-state.2.2.1.val)
    (fun state : FlipState => FlipInvariant dimension assignment parent (assignment root::rest)
      state.1 state.2.1 state.2.2.1 state.2.2.2.1 state.2.2.2.2)
    _ _ _ ?_ h
  rintro ⟨updated,activeColumn,position,stopped,error⟩ hi
  cases stopped with
  | true =>
    unfold sparse_search.flip_sparse_path_loop.body
    simp only [↓reduceIte,WP.spec_ok]
    refine ⟨hi.failure_none,hi.length,?_⟩
    intro row
    have hEnd := hi.finished_exact.mp rfl
    have hv := hi.values row
    rw [hEnd,Assignment.tracePrefixValue_final assignment parent root rest ht hn row] at hv
    exact hv
  | false =>
    apply WP.spec_mono (flip_body_preserves_spec dimension completed predecessor discovery n rootIndex assignment root parent rank input
      rest updated activeColumn position error hi ht hn hPositive)
    intro result hResult
    cases result with
    | done output => exact False.elim hResult
    | cont state => exact hResult

end SubtreeProofs.Rust.SparseSearch

end
