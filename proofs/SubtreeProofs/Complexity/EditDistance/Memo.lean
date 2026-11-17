module

public import SubtreeProofs.Complexity.EditDistance.Specification
public import SubtreeProofs.Complexity.Memo.Bounds
public import SubtreeProofs.Complexity.Memo.Representations
public import Mathlib.Data.Finset.Prod
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Data.Fintype.Fin

/-! A bounded-index edit-distance client of the generic memo interpreter.
Input lists are frozen in the problem. Independent values are minimum edit
costs of suffixes; the body requests three smaller index pairs. Its local
currency counts only three score additions and two minima. Input access,
symbol comparison, index/key construction and source realization are separate
obligations; no complete quadratic runtime is asserted here. -/

@[expose] public section

namespace SubtreeProofs.Complexity.EditDistance

variable {Symbol : Type} [DecidableEq Symbol]

abbrev Key (left right : List Symbol) := Fin (left.length + 1) × Fin (right.length + 1)

def advance (index : Fin (size + 1)) (h : index.val < size) : Fin (size + 1) :=
  ⟨index.val + 1, by omega⟩

def value (left right : List Symbol) (key : Key left right) : Nat :=
  distance (left.drop key.1.val) (right.drop key.2.val)

def body (left right : List Symbol) (key : Key left right) : Memo.Body (Key left right) Nat :=
  if hl : key.1.val < left.length then
    if hr : key.2.val < right.length then
      .ask (key.1, advance key.2 hr) fun insert =>
      .ask (advance key.1 hl, key.2) fun delete =>
      .ask (advance key.1 hl, advance key.2 hr) fun diagonal =>
      .pay 5 (.done (min (insert + 1) (min (delete + 1)
        (diagonal + if left[key.1.val] = right[key.2.val] then 0 else 1))))
    else .done (left.length - key.1.val)
  else .done (right.length - key.2.val)

theorem body_correct (left right : List Symbol) (key : Key left right) :
    (Memo.Body.meaning (value left right) (body left right key)).value = value left right key := by
  by_cases hl : key.1.val < left.length
  · by_cases hr : key.2.val < right.length
    · simp only [body, hl, hr, dite_true, Memo.Body.meaning_ask, Memo.Body.meaning_pay,
        Memo.Body.meaning_done]
      dsimp only [value, advance]
      conv_rhs => rw [List.drop_eq_getElem_cons hl, List.drop_eq_getElem_cons hr, distance]
      rw [← List.drop_eq_getElem_cons hl, ← List.drop_eq_getElem_cons hr]
    · have hz : right.drop key.2.val = [] := List.drop_eq_nil_of_le (by omega)
      simp [body, hl, hr, value, hz]
  · have hz : left.drop key.1.val = [] := List.drop_eq_nil_of_le (by omega)
    simp [body, hl, value, hz]

theorem body_requests (left right : List Symbol) (answer : Key left right → Nat)
    (key : Key left right) :
    (Memo.Body.meaning answer (body left right key)).requests =
      if hl : key.1.val < left.length then
        if hr : key.2.val < right.length then
          [(key.1, advance key.2 hr), (advance key.1 hl, key.2),
            (advance key.1 hl, advance key.2 hr)] else [] else [] := by
  by_cases hl : key.1.val < left.length <;> by_cases hr : key.2.val < right.length <;>
    simp [body, hl, hr]

theorem body_request_bound (left right : List Symbol) (answer : Key left right → Nat)
    (key : Key left right) :
    (Memo.Body.meaning answer (body left right key)).requests.length ≤ 3 := by
  rw [body_requests]
  split
  · split <;> simp
  · simp

def rank (left right : List Symbol) (key : Key left right) : Nat :=
  (left.length - key.1.val) + (right.length - key.2.val)

theorem body_local_bound (left right : List Symbol) (answer : Key left right → Nat)
    (key : Key left right) :
    (Memo.Body.meaning answer (body left right key)).localWork ≤ 5 := by
  by_cases hl : key.1.val < left.length <;> by_cases hr : key.2.val < right.length <;>
    simp [body, hl, hr]

theorem requests_decrease (left right : List Symbol) (key child : Key left right)
    (hc : child ∈ (Memo.Body.meaning (value left right) (body left right key)).requests) :
    rank left right child < rank left right key := by
  rw [body_requests] at hc
  by_cases hl : key.1.val < left.length
  · by_cases hr : key.2.val < right.length
    · simp [hl, hr] at hc
      rcases hc with rfl | rfl | rfl <;> dsimp [rank, advance] <;> omega
    · simp [hl, hr] at hc
  · simp [hl] at hc

def problem (left right : List Symbol) : Memo.Problem (Key left right) Nat where
  value := value left right
  body := body left right
  rank := rank left right
  body_correct := body_correct left right
  requests_decrease := requests_decrease left right

theorem rank_lt_total (left right : List Symbol) (key : Key left right) :
    (problem left right).rank key < left.length + right.length + 1 := by
  dsimp [problem, rank]
  omega

/-- Any conforming representation can evaluate multiple suffix queries with a
shared warm cache. The finite rectangle and request bound are local inputs;
termination, unique expansion and root-plus-body accounting are generic. -/
theorem roots_spec (left right : List Symbol)
    (ops : Memo.CacheOps (Key left right) Nat Storage) (origin : Storage)
    (roots : List (Key left right)) (hv : ops.Valid origin)
    (hs : ops.Sound (value left right) origin) :
    ∃ final, Memo.evalRoots ops (body left right) (left.length + right.length + 1)
        roots ⟨origin, []⟩ = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant ops (problem left right) origin final ∧
      (Memo.Event.completedKeys final.events).length ≤
        (Finset.univ.filter fun key => (ops.contents origin key).isNone).card ∧
      Memo.Event.calls final.events ≤ roots.length +
        3 * (Finset.univ.filter fun key => (ops.contents origin key).isNone).card := by
  have hbound : ∀ key ∈ roots, (problem left right).rank key < left.length + right.length + 1 := by
    intro key _
    dsimp [problem, rank]
    omega
  simpa [problem, Nat.mul_comm] using Memo.roots_envelope ops (problem left right)
    Finset.univ (fun _ => 3) (by simp)
    (fun key _ => body_request_bound left right (value left right) key)
    (left.length + right.length + 1) roots origin hv hs hbound (by simp)

/-- The value returned for the initial index pair is independently optimal. -/
theorem initial_value_optimum (left right : List Symbol) :
    Edits left right (value left right (0, 0)) ∧
      ∀ cost, Edits left right cost → value left right (0, 0) ≤ cost := by
  simpa [value] using distance_optimum left right

end SubtreeProofs.Complexity.EditDistance
