module

public import Aeneas
public import Mathlib.Data.Rat.Defs

/-! Maintained external type model for the ordered-score extraction spike.
The native Rust representation is `f64`; this model deliberately uses exact
rationals. No correspondence between these representations is asserted. -/

@[expose] public section

namespace arithmetic

abbrev Score := ℚ

end arithmetic
