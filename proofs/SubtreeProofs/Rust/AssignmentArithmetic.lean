module

public import Aeneas
public import Aeneas.Std.Scalar.CheckedOps.Add
public import Aeneas.Std.Scalar.CheckedOps.Sub
import all Aeneas.Std.Scalar.CheckedOps.Add
import all Aeneas.Std.Scalar.CheckedOps.Sub

/-!
# Exact checked arithmetic in the assignment core

The pinned signed-operation specifications name their generic functions.
Scoped body imports bridge the public machine aliases to those definitions.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace SubtreeProofs.Rust.AssignmentArithmetic

theorem checked_sub_spec (x y : I128)
    (hmin : I128.min ≤ x.val - y.val) (hmax : x.val - y.val ≤ I128.max) :
    lift (I128.checked_sub x y) ⦃ output => ∃ value, output = some value ∧ value.val = x.val - y.val ⦄ := by
  simp only [lift, WP.spec_ok, I128.checked_sub]
  have h := I128.checked_sub_bv_spec x y
  cases he : core.num.checked_sub_IScalar x y with
  | none =>
    simp only [he] at h
    exact False.elim (h ⟨hmin,hmax⟩)
  | some value =>
    simp only [he] at h
    exact ⟨value, rfl, h.2.2.1⟩

theorem checked_add_spec (x y : I128)
    (hmin : I128.min ≤ x.val + y.val) (hmax : x.val + y.val ≤ I128.max) :
    lift (I128.checked_add x y) ⦃ output => ∃ value, output = some value ∧ value.val = x.val + y.val ⦄ := by
  simp only [lift, WP.spec_ok, I128.checked_add]
  have h := I128.checked_add_bv_spec x y
  cases he : core.num.checked_add_IScalar x y with
  | none =>
    simp only [he] at h
    exact False.elim (h ⟨hmin,hmax⟩)
  | some value =>
    simp only [he] at h
    exact ⟨value, rfl, h.2.2.1⟩

end SubtreeProofs.Rust.AssignmentArithmetic

end
