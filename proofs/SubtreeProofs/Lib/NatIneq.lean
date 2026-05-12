import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace SubtreeProofs.Lib

/--
MATHLIB_CANDIDATE:
If `1 ≤ b`, then multiplying by `b` on the right is inflationary on `Nat`.
-/
theorem nat_le_mul_right_of_one_le {a b : Nat} (hb : 1 ≤ b) :
    a ≤ a * b := by
  calc
    a = a * 1 := by simp
    _ ≤ a * b := Nat.mul_le_mul_left _ hb

/--
MATHLIB_CANDIDATE:
If `1 ≤ a`, then multiplying by `a` on the left is inflationary on `Nat`.
-/
theorem nat_le_mul_left_of_one_le {a b : Nat} (ha : 1 ≤ a) :
    b ≤ a * b := by
  calc
    b = 1 * b := by simp
    _ ≤ a * b := Nat.mul_le_mul_right _ ha

/--
MATHLIB_CANDIDATE:
Package `a ≥ 1` and `b ≥ 1` into `Nat.min a b ≥ 1`.
-/
theorem one_le_min {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ Nat.min a b := by
  exact (Nat.le_min).2 ⟨ha, hb⟩

/--
MATHLIB_CANDIDATE:
If `1 ≤ a`, then `a + 1 ≤ 2 * a`.
-/
theorem add_one_le_two_mul {a : Nat} (ha : 1 ≤ a) :
    a + 1 ≤ 2 * a := by
  calc
    a + 1 ≤ a + a := Nat.add_le_add_left ha _
    _ = 2 * a := by ring

end SubtreeProofs.Lib
