module

public import SubtreeProofs.Rust.SourcePartialLocals
public import Aeneas.Std.Scalar.CheckedOps.Add

/-! Scalar primitives required by the actual evaluator. Checked addition is
related to the pinned native scalar specification in both success and overflow. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource Aeneas.Std

def less32 (left right : Nat) : Option Bool :=
  if left < 2^32 ∧ right < 2^32 then some (decide (left < right)) else none

def checkedAdd32 (left right : Nat) : Option Nat :=
  if left + right < 2^32 then some (left + right) else none

def encodeNumberOption : Option Nat → Value
  | none => .node .optional 0 []
  | some value => .node .optional 1 [.number value]

theorem checkedAdd32_native (left right : U32) :
    checkedAdd32 left.val right.val = (U32.checked_add left right).map (fun value => value.val) := by
  have hs := U32.checked_add_bv_spec left right
  have hmax : U32.max = 2^32 - 1 := by rw [U32.max_eq]; norm_num
  rw [hmax] at hs
  cases hr : U32.checked_add left right with
  | none =>
    rw [hr] at hs
    have hn : ¬left.val + right.val < 2^32 := by omega
    simp only [checkedAdd32, hn, ite_false, Option.map_none]
  | some result =>
    rw [hr] at hs
    have hf : left.val + right.val < 2^32 := by omega
    simp only [checkedAdd32, hf, ite_true, Option.map_some, hs.2.1]

theorem less32_values (left right : U32) :
    less32 left.val right.val = some (decide (left.val < right.val)) := by
  have hl : left.val < 2^32 := left.hmax
  have hr : right.val < 2^32 := right.hmax
  simp only [less32, hl, hr, and_self, ite_true]

theorem checkedAdd32_success {left right result : Nat} (h : checkedAdd32 left right = some result) :
    result = left + right ∧ result < 2^32 := by
  unfold checkedAdd32 at h
  split at h
  next hb => cases h; exact ⟨rfl, hb⟩
  next => cases h

theorem checkedAdd32_overflow (left right : Nat) :
    checkedAdd32 left right = none ↔ 2^32 ≤ left + right := by
  simp [checkedAdd32]

end SubtreeProofs.Rust.SourceEval
