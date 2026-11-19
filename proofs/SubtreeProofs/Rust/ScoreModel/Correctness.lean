module

public import SubtreeProofs.Rust.ScoreModel.Funs
public import SubtreeProofs.Paper2004.AffinityIsomorphismDP
import Mathlib.Tactic

/-! The actual extracted local step, under the explicitly idealized rational
primitive model. This does not prove the production DP, memo or native floats. -/

@[expose] public section

open Aeneas Aeneas.Std Result
open score_model

namespace SubtreeProofs.Rust.ScoreModel

def select (best candidate : Candidate) : Candidate :=
  if best.score < candidate.score then candidate else best

theorem improve_eq (best candidate : Candidate) :
    improve best candidate = .ok (select best candidate) := by
  simp [improve, arithmetic.greater, select]
  split_ifs <;> rfl

theorem select_score (best candidate : Candidate) :
    (select best candidate).score = max best.score candidate.score := by
  unfold select
  split
  · rename_i h
    exact (max_eq_right (le_of_lt h)).symm
  · rename_i h
    exact (max_eq_left (le_of_not_gt h)).symm

theorem select_preserves (P : Candidate → Prop) {best candidate : Candidate}
    (hBest : P best) (hCandidate : P candidate) : P (select best candidate) := by
  unfold select
  split <;> assumption

theorem improve_tie (best candidate : Candidate) (h : best.score = candidate.score) :
    improve best candidate = .ok best := by
  simp [improve_eq, select, h]

def empty : Candidate := ⟨0, 0#u32⟩

def base (dropRight dropLeft : Candidate) : Candidate :=
  select (select empty dropRight) dropLeft

def matched (head tail affinity : ℚ) (witness : U32) : Candidate :=
  ⟨head + tail + affinity, witness⟩

def step (dropRight dropLeft : Candidate) (head tail affinity : ℚ)
    (witness : U32) : Candidate :=
  if 0 < affinity then select (base dropRight dropLeft) (matched head tail affinity witness)
  else base dropRight dropLeft

/-- Every call to the translated Rust step succeeds under the exact model;
the returned candidate includes the prescribed original witness identifier. -/
theorem level_step_eq (dropRight dropLeft : Candidate) (head tail affinity : ℚ)
    (witness : U32) :
    level_step dropRight dropLeft head tail affinity witness =
      .ok (step dropRight dropLeft head tail affinity witness) := by
  simp [level_step, arithmetic.zero, arithmetic.positive, arithmetic.add,
    improve_eq, step, base, empty, matched]
  split_ifs <;> rfl

/-- Independent scalar optimum for the locally available candidates. The
matched candidate is eligible precisely when its root affinity is positive. -/
theorem level_step_score (dropRight dropLeft : Candidate) (head tail affinity : ℚ)
    (witness : U32) :
    ∃ result, level_step dropRight dropLeft head tail affinity witness = .ok result ∧
      result.score = if 0 < affinity then
        max (max (max 0 dropRight.score) dropLeft.score) (head + tail + affinity)
      else max (max 0 dropRight.score) dropLeft.score := by
  refine ⟨step dropRight dropLeft head tail affinity witness,
    level_step_eq _ _ _ _ _ _, ?_⟩
  unfold step
  split <;> simp [select_score, base, empty, matched]

/-- Any witness invariant holding for each eligible candidate survives the
actual extracted selection. The callers still have to prove these premises. -/
theorem level_step_preserves (P : Candidate → Prop) (dropRight dropLeft : Candidate)
    (head tail affinity : ℚ) (witness : U32) (hEmpty : P empty)
    (hRight : P dropRight) (hLeft : P dropLeft)
    (hMatched : 0 < affinity → P (matched head tail affinity witness)) :
    ∃ result, level_step dropRight dropLeft head tail affinity witness = .ok result ∧ P result := by
  refine ⟨step dropRight dropLeft head tail affinity witness,
    level_step_eq _ _ _ _ _ _, ?_⟩
  have hBase : P (base dropRight dropLeft) :=
    select_preserves P (select_preserves P hEmpty hRight) hLeft
  unfold step
  split
  · rename_i h
    exact select_preserves P hBase (hMatched h)
  · exact hBase

open SubtreeProofs.Paper2004.AnnotatedIso in
/-- With the mathematically correct child scores, the extracted local step
has the independent rooted recurrence's optimum score. This leaves computation
of those children, state representations, memoization and arena links to O01/O02. -/
theorem level_step_recurrence_score {L R : Type*} (affinity : L → R → ℚ)
    (a : L) (b : R) (lh lt : Word L) (rh rt : Word R)
    (dropRight dropLeft : Candidate) (witness : U32)
    (hRight : dropRight.score = score affinity (AffinityDP.level affinity (.node a lh lt) rt))
    (hLeft : dropLeft.score = score affinity (AffinityDP.level affinity lt (.node b rh rt))) :
    ∃ result, level_step dropRight dropLeft
        (score affinity (AffinityDP.level affinity lh rh))
        (score affinity (AffinityDP.level affinity lt rt)) (affinity a b) witness = .ok result ∧
      result.score = score affinity (AffinityDP.level affinity (.node a lh lt) (.node b rh rt)) := by
  obtain ⟨result, hRun, hScore⟩ := level_step_score dropRight dropLeft
    (score affinity (AffinityDP.level affinity lh rh))
    (score affinity (AffinityDP.level affinity lt rt)) (affinity a b) witness
  refine ⟨result, hRun, ?_⟩
  have hNonneg : 0 ≤ score affinity (AffinityDP.level affinity (.node a lh lt) rt) :=
    (AffinityDP.level_sound affinity (.node a lh lt) rt).2.2.score_nonnegative
  rw [hRight, hLeft, max_eq_right hNonneg] at hScore
  rw [hScore, AffinityDP.level]
  split_ifs <;> simp [AffinityDP.score_choose, score]

end SubtreeProofs.Rust.ScoreModel
