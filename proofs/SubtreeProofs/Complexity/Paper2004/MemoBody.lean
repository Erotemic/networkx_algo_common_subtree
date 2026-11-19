module

public import SubtreeProofs.Complexity.Memo.Interpreter
public import SubtreeProofs.Paper2004.MemoizedDynamicProgram

/-!
# The existing four-request LV recurrence as a memo body

The independent score remains `paperLcs`. This body has the exact request order
of the maintained numerical evaluator. Its local currency counts only the two
score additions and two maxima; body/key construction, tests, dictionary work
and source realization remain separate obligations. No Rust runtime follows
from this request-body adapter.
-/

@[expose] public section

namespace SubtreeProofs.Complexity.Paper2004

open SubtreeProofs.Paper2004
open SubtreeProofs.Paper2004.OrderedTree
open SubtreeProofs.Complexity.Memo

/-- Freeze the independently proved recurrence as the cache's value meaning. -/
def score (key : MemoKey) : Nat := paperLcs key.1 key.2

/-- Four sequential requests, in the actual evaluator's order. -/
def body (key : MemoKey) : Body MemoKey Nat :=
  let (left, right) := key
  if left = 0 then .done 0 else
  if right = 0 then .done 0 else
    .ask (left.insidePart, right.insidePart) fun head =>
    .ask (left.outsidePart, right.outsidePart) fun tail =>
    .ask (left.insidePart + left.outsidePart, right) fun dropLeft =>
    .ask (left, right.insidePart + right.outsidePart) fun dropRight =>
    .pay 4 (.done (max (max (head + tail + 1) dropLeft) dropRight))

/-- The body computes the established independent recurrence, not an optimum
introduced by defining it to be the output of the memo interpreter. -/
theorem body_correct (left right : DyckWord) :
    (Body.meaning score (body (left, right))).value = paperLcs left right := by
  by_cases hl : left = 0
  · rw [paperLcs]
    simp [body, hl]
  · by_cases hr : right = 0
    · rw [paperLcs]
      simp [body, hl, hr]
    · conv_rhs => rw [paperLcs]
      simp [body, hl, hr, score]

/-- Direct request occurrences retain order and multiplicity for any answers. -/
theorem body_requests (answer : MemoKey → Nat) (left right : DyckWord) :
    (Body.meaning answer (body (left, right))).requests =
      if left = 0 ∨ right = 0 then [] else
        [(left.insidePart, right.insidePart), (left.outsidePart, right.outsidePart),
          (left.insidePart + left.outsidePart, right), (left, right.insidePart + right.outsidePart)] := by
  by_cases hl : left = 0 <;> by_cases hr : right = 0 <;> simp [body, hl, hr]

theorem body_request_bound (answer : MemoKey → Nat) (left right : DyckWord) :
    (Body.meaning answer (body (left, right))).requests.length ≤ 4 := by
  rw [body_requests]
  split <;> simp

theorem body_local_bound (answer : MemoKey → Nat) (left right : DyckWord) :
    (Body.meaning answer (body (left, right))).localWork ≤ 4 := by
  by_cases hl : left = 0 <;> by_cases hr : right = 0 <;> simp [body, hl, hr]

/-- Every requested state is smaller under the existing semilength rank. -/
theorem requests_decrease (answer : MemoKey → Nat) (left right : DyckWord)
    (child : MemoKey) (hc : child ∈ (Body.meaning answer (body (left, right))).requests) :
    child.1.semilength + child.2.semilength < left.semilength + right.semilength := by
  rw [body_requests] at hc
  by_cases hz : left = 0 ∨ right = 0
  · simp [hz] at hc
  · have hl : left ≠ 0 := fun h => hz (Or.inl h)
    have hr : right ≠ 0 := fun h => hz (Or.inr h)
    have hleft := BalancedDecomposition.contracted_semilength hl
    have hright := BalancedDecomposition.contracted_semilength hr
    simp only [DyckWord.semilength_add] at hleft hright
    simp [hz] at hc
    rcases hc with rfl | rfl | rfl | rfl <;>
      simp only [DyckWord.semilength_add] <;> omega

/-- The concrete LV recurrence fits the generic evaluator without any tree
imports in the generic modules or assumed cache-miss/runtime conclusion. -/
def problem : Problem MemoKey Nat where
  value := score
  body := body
  rank := fun key => key.1.semilength + key.2.semilength
  body_correct := fun key => body_correct key.1 key.2
  requests_decrease := fun key child hc => requests_decrease score key.1 key.2 child hc

end SubtreeProofs.Complexity.Paper2004
