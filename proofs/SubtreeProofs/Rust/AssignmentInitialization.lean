module

public import SubtreeProofs.Rust.Generated.VerifiedAssignmentCore
import Mathlib.Tactic

/-!
# Actual assignment-core initialization loops

A shared proof covers the four translated loops that construct zero
potentials, unmatched indices, absent slacks and unused-column flags.
-/

@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow
open verified_assignment_core

namespace SubtreeProofs.Rust.AssignmentInitialization

/-- The common body of the four actual translated initializer loops. -/
def fillBody {T : Type*} (len : Usize) (value : T) (state : alloc.vec.Vec T × Usize) :
    Result (ControlFlow (alloc.vec.Vec T × Usize) (alloc.vec.Vec T)) := do
  if state.2 < len then
    let result ← alloc.vec.Vec.push state.1 value
    let index ← state.2 + 1#usize
    ok (cont (result,index))
  else ok (done state.1)

/-- The reserve-free push loop terminates with exactly the requested contents;
scalar increments and modeled vector size checks succeed. -/
theorem fill_loop_spec {T : Type*} (len : Usize) (value : T) :
    loop (fillBody len value) (alloc.vec.Vec.new T, 0#usize) ⦃ result =>
      result.val = List.replicate len.val value ⦄ := by
  apply loop.spec_decr_nat (fun state => len.val - state.2.val)
    (fun state => state.2.val ≤ len.val ∧ state.1.val = List.replicate state.2.val value)
    _ _ _ ?_ (by simp)
  rintro ⟨result,index⟩ ⟨hi, hrep⟩
  unfold fillBody
  split
  · rename_i hlt
    have hpush : result.val.length < Usize.max := by
      rw [hrep, List.length_replicate]
      scalar_tac
    apply WP.spec_bind (alloc.vec.Vec.push_spec result value hpush)
    intro result1 hresult1
    apply WP.spec_bind (Usize.add_spec (x := index) (y := 1#usize) (by scalar_tac))
    intro index1 hindex1
    simp only [WP.spec_ok]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · scalar_tac
    · rw [hresult1, hrep]
      simp only [UScalar.ofNatCore_val_eq] at hindex1
      rw [hindex1, List.replicate_succ']
    · scalar_tac
  · rename_i hnot
    simp only [WP.spec_ok]
    have he : index.val = len.val := by scalar_tac
    exact hrep.trans (congrArg (fun n => List.replicate n value) he)

/-- Actual Rust potential initialization, not a replacement list constructor. -/
theorem zeros_i128_spec (len : Usize) : zeros_i128 len ⦃ result =>
    result.val = List.replicate len.val 0#i128 ⦄ := by
  exact fill_loop_spec len 0#i128

theorem zeros_usize_spec (len : Usize) : zeros_usize len ⦃ result =>
    result.val = List.replicate len.val 0#usize ⦄ := by
  exact fill_loop_spec len 0#usize

theorem absent_costs_spec (len : Usize) : absent_costs len ⦃ result =>
    result.val = List.replicate len.val none ⦄ := by
  exact fill_loop_spec len (none : Option I128)

theorem unused_columns_spec (len : Usize) : unused_columns len ⦃ result =>
    result.val = List.replicate len.val false ⦄ := by
  exact fill_loop_spec len false

end SubtreeProofs.Rust.AssignmentInitialization

end
