import SubtreeProofs.Rust.ScoreModel.Correctness

open Aeneas Aeneas.Std score_model
open SubtreeProofs.Rust.ScoreModel

deriving instance DecidableEq for Candidate

-- Strict improvement retains the first witness in a three-way positive tie.
example : level_step ⟨4, 1#u32⟩ ⟨4, 2#u32⟩ 1 1 2 3#u32 =
    .ok ⟨4, 1#u32⟩ := by
  rw [level_step_eq]
  exact congrArg Result.ok (by decide +kernel)

-- Empty wins zero ties and zero root affinity forbids the match altogether.
example : level_step ⟨0, 1#u32⟩ ⟨0, 2#u32⟩ 100 100 0 3#u32 =
    .ok ⟨0, 0#u32⟩ := by
  rw [level_step_eq]
  exact congrArg Result.ok (by decide +kernel)

-- The exact primitive model can compare fractional scores.
example : level_step ⟨4, 1#u32⟩ ⟨3, 2#u32⟩ (3/2) 1 2 3#u32 =
    .ok ⟨9/2, 3#u32⟩ := by
  rw [level_step_eq]
  exact congrArg Result.ok (by decide +kernel)

-- The rational model preserves an integer sum that native f64 loses.
example : level_step ⟨9007199254740992, 1#u32⟩ ⟨0, 2#u32⟩
    9007199254740992 0 1 3#u32 = .ok ⟨9007199254740993, 3#u32⟩ := by
  rw [level_step_eq]
  exact congrArg Result.ok (by decide +kernel)

-- Existing independent whole-forest optimum theorems accept both exact domains.
open SubtreeProofs.Paper2004.AnnotatedIso in
example (affinity : Nat → Nat → ℚ) (left right : Word Nat) :
    IsMaximumLevel affinity (AffinityDP.level affinity left right) left right :=
  AffinityDP.level_correct affinity left right

open SubtreeProofs.Paper2004.AnnotatedIso in
example (affinity : Nat → Nat → ℤ) (left right : Word Nat) :
    IsMaximumAny affinity (AffinityDP.anywhere affinity left right) left right :=
  AffinityDP.anywhere_correct affinity left right

#print axioms level_step_eq
#print axioms level_step_score
#print axioms level_step_preserves
#print axioms level_step_recurrence_score
