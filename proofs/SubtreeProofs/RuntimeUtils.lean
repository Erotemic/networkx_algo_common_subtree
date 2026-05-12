import SubtreeProofs.Lib

namespace LozanoValiente2004
namespace RuntimeUtils

/-- If `1 ≤ b`, then multiplying by `b` on the right is inflationary on `Nat`. -/
theorem nat_le_mul_right_of_one_le {a b : Nat} (hb : 1 ≤ b) :
    a ≤ a * b := by
  exact SubtreeProofs.Lib.nat_le_mul_right_of_one_le hb

/-- If `1 ≤ b`, then multiplying by `b` on the left is inflationary on `Nat`. -/
theorem nat_le_mul_left_of_one_le {a b : Nat} (ha : 1 ≤ a) :
    b ≤ a * b := by
  exact SubtreeProofs.Lib.nat_le_mul_left_of_one_le ha

/-- Package `a ≥ 1` and `b ≥ 1` into `min a b ≥ 1`. -/
theorem one_le_min {a b : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) :
    1 ≤ Nat.min a b := by
  exact SubtreeProofs.Lib.one_le_min ha hb

/-- If `1 ≤ a`, then `a + 1 ≤ 2*a`. -/
theorem add_one_le_two_mul {a : Nat} (ha : 1 ≤ a) :
    a + 1 ≤ 2 * a := by
  exact SubtreeProofs.Lib.add_one_le_two_mul ha

end RuntimeUtils
end LozanoValiente2004
