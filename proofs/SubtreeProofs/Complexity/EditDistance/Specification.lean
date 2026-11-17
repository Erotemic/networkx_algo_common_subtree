module

public import Mathlib.Data.List.Basic

/-! An independent edit specification and minimum-cost recurrence.
Edits consume input/output heads: insertion, deletion and replacement cost one;
copying an equal symbol costs zero. No memo interpreter appears in this file. -/

@[expose] public section

namespace SubtreeProofs.Complexity.EditDistance

inductive Edits : List Symbol → List Symbol → Nat → Prop where
  | empty : Edits [] [] 0
  | insert (symbol : Symbol) : Edits left right cost → Edits left (symbol :: right) (cost + 1)
  | delete (symbol : Symbol) : Edits left right cost → Edits (symbol :: left) right (cost + 1)
  | copy (symbol : Symbol) : Edits left right cost → Edits (symbol :: left) (symbol :: right) cost
  | replace (first second : Symbol) :
      Edits left right cost → Edits (first :: left) (second :: right) (cost + 1)

def distance [DecidableEq Symbol] : List Symbol → List Symbol → Nat
  | [], right => right.length
  | first :: left, [] => left.length + 1
  | first :: left, second :: right =>
    min (distance (first :: left) right + 1)
      (min (distance left (second :: right) + 1)
        (distance left right + if first = second then 0 else 1))
termination_by left right => left.length + right.length

@[simp] theorem distance_nil_left [DecidableEq Symbol] (right : List Symbol) :
    distance [] right = right.length := by rw [distance]

@[simp] theorem distance_nil_right [DecidableEq Symbol] (left : List Symbol) :
    distance left [] = left.length := by cases left <;> simp only [distance, List.length_nil, List.length_cons]

theorem distance_insert [DecidableEq Symbol] (left right : List Symbol) (symbol : Symbol) :
    distance left (symbol :: right) ≤ distance left right + 1 := by
  cases left with
  | nil => simp
  | cons first rest =>
    conv_lhs => rw [distance]
    exact Nat.min_le_left _ _

theorem distance_delete [DecidableEq Symbol] (left right : List Symbol) (symbol : Symbol) :
    distance (symbol :: left) right ≤ distance left right + 1 := by
  cases right with
  | nil => simp
  | cons first rest =>
    conv_lhs => rw [distance]
    exact Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_left _ _)

theorem distance_copy [DecidableEq Symbol] (left right : List Symbol) (symbol : Symbol) :
    distance (symbol :: left) (symbol :: right) ≤ distance left right := by
  conv_lhs => rw [distance]
  simpa using Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right
    (distance left (symbol :: right) + 1) (distance left right + if symbol = symbol then 0 else 1))

theorem distance_replace [DecidableEq Symbol] (left right : List Symbol) (first second : Symbol) :
    distance (first :: left) (second :: right) ≤ distance left right + 1 := by
  conv_lhs => rw [distance]
  have h := Nat.le_trans (Nat.min_le_right (distance (first :: left) right + 1) _)
    (Nat.min_le_right (distance left (second :: right) + 1)
      (distance left right + if first = second then 0 else 1))
  have hi : (if first = second then 0 else 1 : Nat) ≤ 1 := by split <;> omega
  exact Nat.le_trans h (Nat.add_le_add_left hi _)

/-- Every independently specified edit sequence costs at least the recurrence. -/
theorem distance_le_edits [DecidableEq Symbol] {left right : List Symbol} {cost : Nat}
    (edits : Edits left right cost) : distance left right ≤ cost := by
  induction edits with
  | empty => simp
  | insert symbol _ ih => exact Nat.le_trans (distance_insert _ _ symbol) (Nat.add_le_add_right ih 1)
  | delete symbol _ ih => exact Nat.le_trans (distance_delete _ _ symbol) (Nat.add_le_add_right ih 1)
  | copy symbol _ ih => exact Nat.le_trans (distance_copy _ _ symbol) ih
  | replace first second _ ih =>
    exact Nat.le_trans (distance_replace _ _ first second) (Nat.add_le_add_right ih 1)

/-- The minimum is attained by valid edits, not merely a lower bound. -/
theorem edits_distance [DecidableEq Symbol] (left right : List Symbol) :
    Edits left right (distance left right) := by
  cases left with
  | nil =>
    cases right with
    | nil => simpa using (Edits.empty : Edits ([] : List Symbol) [] 0)
    | cons symbol right => simpa using Edits.insert symbol (edits_distance [] right)
  | cons first left =>
    cases right with
    | nil => simpa using Edits.delete first (edits_distance left [])
    | cons second right =>
      rw [distance]
      by_cases hi : distance (first :: left) right + 1 ≤
          min (distance left (second :: right) + 1)
            (distance left right + if first = second then 0 else 1)
      · rw [Nat.min_eq_left hi]
        exact .insert second (edits_distance (first :: left) right)
      · rw [Nat.min_eq_right (by omega)]
        by_cases hd : distance left (second :: right) + 1 ≤
            distance left right + if first = second then 0 else 1
        · rw [Nat.min_eq_left hd]
          exact .delete first (edits_distance left (second :: right))
        · rw [Nat.min_eq_right (by omega)]
          by_cases he : first = second
          · subst second
            simpa using Edits.copy first (edits_distance left right)
          · simpa [he] using Edits.replace first second (edits_distance left right)
termination_by left.length + right.length

/-- Independent minimum-cost edit contract consumed by the memo client. -/
theorem distance_optimum [DecidableEq Symbol] (left right : List Symbol) :
    Edits left right (distance left right) ∧
      ∀ cost, Edits left right cost → distance left right ≤ cost :=
  ⟨edits_distance left right, fun _ he => distance_le_edits he⟩

end SubtreeProofs.Complexity.EditDistance
