module

public import SubtreeProofs.Shared.RectangularAssignment
public import SubtreeProofs.Shared.AssignmentPotentials
public import Mathlib.Logic.Function.Basic
public import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Tactic

/-!
# Restricting transposed row-deletion repair to old occupied columns

The production matcher replaces the deleted row by a zero-cost dummy and
repairs a square problem on the old occupied columns. A root-normalized
repaired dual extends to every original column and certifies a global
rectangular optimum. This is exact ordered-arithmetic mathematics, not an
IEEE-754 or actual-source refinement theorem for the f64 caller.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

variable {A B K : Type*} [Fintype A] [Fintype B] [DecidableEq A]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def zeroRow (matrix : A → B → K) (removed row : A) (column : B) : K :=
  if row = removed then 0 else matrix row column

/-- The finite minimum used by the source dummy-row initialization. The root
witness supplies nonemptiness; no infinity element is added to the ring. -/
noncomputable def dummyBaseline (occupied : A ↪ B) (columns : B → K) (root : A) : K :=
  Finset.univ.inf' ⟨root,Finset.mem_univ _⟩ (fun column => -columns (occupied column))

omit [Fintype B] [DecidableEq A] in
/-- Nonpositive old column potentials make the new dummy baseline nonnegative
and feasible against every old occupied column. -/
theorem dummyBaseline_spec (occupied : A ↪ B) (columns : B → K) (root : A)
    (hColumns : ∀ column, columns column ≤ 0) :
    0 ≤ dummyBaseline occupied columns root ∧
      ∀ column, dummyBaseline occupied columns root+columns (occupied column) ≤ 0 := by
  classical
  constructor
  · unfold dummyBaseline
    apply Finset.le_inf'
    intro column _
    exact neg_nonneg.mpr (hColumns _)
  · intro column
    have h : dummyBaseline occupied columns root ≤ -columns (occupied column) := by
      unfold dummyBaseline
      exact Finset.inf'_le _ (Finset.mem_univ column)
    linarith

omit [Fintype B] in
/-- The source's zero-row replacement is feasible initially, and all nonroot
old diagonal pairs remain tight. No new restricted optimum is supplied. -/
theorem dummy_initialization (matrix : A → B → K) (occupied : A ↪ B)
    (oldRows : A → K) (oldColumns : B → K) (root : A)
    (hFeasible : RectangularFeasible matrix oldRows oldColumns)
    (hColumns : ∀ column, oldColumns column ≤ 0)
    (hTight : RectangularTight matrix oldRows oldColumns occupied) :
    Feasible (zeroRow (fun row column => matrix row (occupied column)) root)
      (Function.update oldRows root (dummyBaseline occupied oldColumns root)) (fun column => oldColumns (occupied column)) ∧
    ∀ row, row ≠ root →
      Function.update oldRows root (dummyBaseline occupied oldColumns root) row+oldColumns (occupied row) =
        zeroRow (fun row column => matrix row (occupied column)) root row row := by
  obtain ⟨_,hDummy⟩ := dummyBaseline_spec occupied oldColumns root hColumns
  constructor
  · intro row column
    by_cases he : row = root
    · subst row
      simpa only [Function.update_self,zeroRow,↓reduceIte] using hDummy column
    · simpa only [Function.update_of_ne he,zeroRow,he,↓reduceIte] using hFeasible row (occupied column)
  · intro row he
    simpa only [Function.update_of_ne he,zeroRow,he,↓reduceIte] using hTight row

omit [Fintype A] in
/-- Root membership in every dual update maintains the exact root increment;
other rows increase by at most that accumulated amount. -/
theorem warm_rows_adjust (oldRows rows : A → K) (root : A) (baseline increment delta : K)
    (selected : Finset A) (hSelected : root ∈ selected) (hDelta : 0 ≤ delta)
    (hRoot : rows root = baseline+increment)
    (hRows : ∀ row, row ≠ root → rows row ≤ oldRows row+increment) :
    adjustRows rows selected delta root = baseline+(increment+delta) ∧
      ∀ row, row ≠ root → adjustRows rows selected delta row ≤ oldRows row+(increment+delta) := by
  constructor
  · simp only [adjustRows,hSelected,↓reduceIte,hRoot]
    ring
  · intro row hr
    have h := hRows row hr
    by_cases hs : row ∈ selected <;> simp only [adjustRows,hs,↓reduceIte] <;> linarith

/-- A feasible/tight repair on old occupied columns is globally optimal after
the row deletion. The only work-growth premise is the per-row warm-update
invariant; no global optimum or restricted/unrestricted equivalence is assumed.
The returned injection labels columns with their original occupied indices. -/
theorem transposed_repair_global_minimum (matrix : A → B → K) (occupied : A ↪ B)
    (oldRows : A → K) (oldColumns : B → K) (root : A)
    (rows columns : A → K) (chosen : Equiv.Perm A) (baseline increment : K)
    (hOldFeasible : RectangularFeasible matrix oldRows oldColumns)
    (hOldUnused : ∀ column, (¬ ∃ row, occupied row = column) → oldColumns column = 0)
    (hFeasible : Feasible (zeroRow (fun row column => matrix row (occupied column)) root) rows columns)
    (hTight : Tight (zeroRow (fun row column => matrix row (occupied column)) root) rows columns chosen)
    (hBaseline : 0 ≤ baseline) (hRoot : rows root = baseline+increment)
    (hRows : ∀ row, row ≠ root → rows row ≤ oldRows row+increment) :
    IsMinimumInjection (zeroRow matrix root) (chosen.toEmbedding.trans occupied) := by
  classical
  let normalizedRows := fun row => rows row-rows root
  let normalizedColumns : B → K := Function.extend occupied (fun column => columns column+rows root) (fun _ => 0)
  have hInside : ∀ column, normalizedColumns (occupied column) = columns column+rows root := by
    intro column
    exact occupied.injective.extend_apply _ _ column
  have hOutside : ∀ column, (¬ ∃ row, occupied row = column) → normalizedColumns column = 0 := by
    intro column hn
    exact Function.extend_apply' _ _ _ hn
  have hNonroot : ∀ row, row ≠ root → normalizedRows row ≤ oldRows row := by
    intro row hr
    have h := hRows row hr
    dsimp only [normalizedRows]
    rw [hRoot]
    linarith
  have hGlobalFeasible : RectangularFeasible (zeroRow matrix root) normalizedRows normalizedColumns := by
    intro row column
    by_cases hi : ∃ original, occupied original = column
    · obtain ⟨original,rfl⟩ := hi
      rw [hInside]
      have h := hFeasible row original
      change rows row-rows root+(columns original+rows root) ≤ zeroRow matrix root row (occupied original)
      have hc : zeroRow (fun row column => matrix row (occupied column)) root row original = zeroRow matrix root row (occupied original) := by
        simp only [zeroRow]
      rw [hc] at h
      linarith
    · rw [hOutside column hi]
      by_cases hr : row = root
      · subst row
        simp only [normalizedRows,sub_self,zeroRow,↓reduceIte,add_zero,le_refl]
      · have h := hOldFeasible row column
        rw [hOldUnused column hi,add_zero] at h
        have hn := hNonroot row hr
        simpa only [zeroRow,hr,↓reduceIte,add_zero] using hn.trans h
  have hGlobalColumns : ∀ column, normalizedColumns column ≤ 0 := by
    intro column
    by_cases hi : ∃ original, occupied original = column
    · obtain ⟨original,rfl⟩ := hi
      rw [hInside]
      have h := hFeasible root original
      simp only [zeroRow,↓reduceIte] at h
      linarith
    · rw [hOutside column hi]
  have hGlobalTight : RectangularTight (zeroRow matrix root) normalizedRows normalizedColumns (chosen.toEmbedding.trans occupied) := by
    intro row
    change normalizedRows row+normalizedColumns (occupied (chosen row)) = zeroRow matrix root row (occupied (chosen row))
    rw [hInside]
    have h := hTight row
    change rows row-rows root+(columns (chosen row)+rows root) = zeroRow matrix root row (occupied (chosen row))
    have hc : zeroRow (fun row column => matrix row (occupied column)) root row (chosen row) = zeroRow matrix root row (occupied (chosen row)) := by
      simp only [zeroRow]
    rw [hc] at h
    linarith
  have hGlobalUnused : ∀ column, (¬ ∃ row, (chosen.toEmbedding.trans occupied) row = column) → normalizedColumns column = 0 := by
    intro column hn
    apply hOutside column
    rintro ⟨original,he⟩
    apply hn
    refine ⟨chosen.symm original,?_⟩
    simpa only [Function.Embedding.trans_apply,Equiv.toEmbedding_apply,Equiv.apply_symm_apply] using he
  exact minimum_injection_of_feasible_tight hGlobalFeasible hGlobalColumns hGlobalTight hGlobalUnused

end SubtreeProofs.Assignment

end
