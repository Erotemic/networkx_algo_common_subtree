import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace SubtreeProofs.Lib

/--
Expected-cost assumptions for proxy dictionary/array primitives.

These are explicit hypotheses, not hidden axioms.
-/
structure RuntimeAssumptions where
  cLookup : Real
  cInsert : Real
  cRead   : Real
  cWrite  : Real
  hLookup_nonneg : 0 ≤ cLookup
  hInsert_nonneg : 0 ≤ cInsert
  hRead_nonneg   : 0 ≤ cRead
  hWrite_nonneg  : 0 ≤ cWrite

/-- Aggregated per-sequence coding coefficient. -/
def RuntimeAssumptions.cCode (A : RuntimeAssumptions) : Real := A.cLookup + A.cInsert

/-- Aggregated per-DP-cell coefficient (`4` reads + `1` write). -/
def RuntimeAssumptions.cDP (A : RuntimeAssumptions) : Real := 4 * A.cRead + A.cWrite

/-- Overall multiplicative constant used in runtime bounds. -/
def runtimeConstant (A : RuntimeAssumptions) : Real := 2 * A.cCode + A.cDP

theorem cCode_nonneg (A : RuntimeAssumptions) : 0 ≤ A.cCode := by
  exact add_nonneg A.hLookup_nonneg A.hInsert_nonneg

theorem cDP_nonneg (A : RuntimeAssumptions) : 0 ≤ A.cDP := by
  have h4 : (0 : Real) ≤ 4 := by norm_num
  exact add_nonneg (mul_nonneg h4 A.hRead_nonneg) A.hWrite_nonneg

theorem runtimeConstant_nonneg (A : RuntimeAssumptions) : 0 ≤ runtimeConstant A := by
  have h2 : (0 : Real) ≤ 2 := by norm_num
  exact add_nonneg (mul_nonneg h2 (cCode_nonneg A)) (cDP_nonneg A)

end SubtreeProofs.Lib
