import SubtreeProofs.Complexity.Memo.Bounds
import SubtreeProofs.Complexity.Memo.Representations
import SubtreeProofs.Complexity.Paper2004.MemoBody
import SubtreeProofs.Complexity.Paper2004.MemoCorrespondence

/-! Interpreter discriminator cases, not a replacement for W05's independent
edit-distance client or correspondence with the existing LV evaluator. -/

namespace MemoTests

open SubtreeProofs.Complexity.Memo

private def answer (key : Fin 3) : Nat := key.val + 1

private def body (key : Fin 3) : Body (Fin 3) Nat :=
  if key.val = 0 then .done 1 else
  if key.val = 1 then
    .ask 0 fun first => .ask 0 fun second => .pay 1 (.done (first + second))
  else .ask 0 fun first =>
    if first = 1 then .ask 1 fun second => .pay 1 (.done (first + second)) else .done 0

private def problem : Problem (Fin 3) Nat where
  value := answer
  body := body
  rank := Fin.val
  body_correct := by intro key; fin_cases key <;> decide
  requests_decrease := by
    intro key child hm
    fin_cases key <;> fin_cases child <;> simp_all [body, answer, Body.meaning, Body.run, bind, pure]

private def listOps := (ListCache.ops : CacheOps (Fin 3) Nat (List (Fin 3 × Nat)))
private def arrayOps := DirectCache.ops 3 Nat

private def observe (result : EStateM.Result Unit (EvalState (Fin 3) Storage) (List Nat)) :
    Option (List Nat × Nat × List (Fin 3) × Nat × Nat × Nat) :=
  match result with
  | .error _ _ => none
  | .ok values state => some (values, Event.calls state.events,
      Event.completedKeys state.events, Event.lookupWork state.events,
      Event.insertionWork state.events, Event.localWork state.events)

-- Empty roots execute no requests, even with zero fuel.
example : observe (evalRoots listOps body 0 [] ⟨[], []⟩) = some ([], 0, [], 0, 0, 0) := by decide +kernel

-- Repeated children and roots count as calls, but each absent key expands once.
example : observe (evalRoots listOps body 3 [2, 2] ⟨[], []⟩) =
    some ([3, 3], 6, [2, 1, 0], 4, 3, 2) := by decide +kernel

-- The same body and combinatorics, with different concrete lookup work.
example : observe (evalRoots arrayOps body 3 [2, 2] ⟨(DirectCache.buildEmpty Nat 3).1, []⟩) =
    some ([3, 3], 6, [2, 1, 0], 6, 3, 2) := by decide +kernel

-- A valid fully warm cache succeeds with zero fuel; roots retain multiplicity.
example : observe (evalRoots listOps body 0 [2, 2] ⟨[(0, 1), (1, 2), (2, 3)], []⟩) =
    some ([3, 3], 2, [], 6, 0, 0) := by decide +kernel

example : observe (evalRoots arrayOps body 0 [2, 2] ⟨#[some 1, some 2, some 3], []⟩) =
    some ([3, 3], 2, [], 2, 0, 0) := by decide +kernel

-- Initialization is explicitly charged rather than silently free.
example : (ListCache.buildEmpty : List (Fin 3 × Nat) × Nat).2 = 1 := rfl
example : (DirectCache.buildEmpty Nat 3).2 = 4 := rfl

-- An insufficient cold miss fails; the completed-run theorem requires descent fuel.
example : observe (evalRoots listOps body 0 [2] ⟨[], []⟩) = none := by decide +kernel

-- An unsound warm answer changes a continuation and invalidates correctness.
example : observe (evalRoots listOps body 3 [2] ⟨[(0, 0)], []⟩) =
    some ([0], 2, [2], 2, 1, 0) := by decide +kernel

example : ¬ listOps.Sound answer [(0, 0)] := by
  intro hs
  have he := hs 0 0 (by decide)
  simp [answer] at he

-- A value-correct adversary that resets the cache before every sibling request
-- repeats the base expansion. It violates the sequential sharing contract.
private def resetRequest (child : Fin 3) : EStateM Unit (EvalState (Fin 3) (List (Fin 3 × Nat))) Nat :=
  fun state => eval listOps body 3 child { state with cache := [] }

private def broken : EStateM.Result Unit (EvalState (Fin 3) (List (Fin 3 × Nat))) Nat :=
  match Body.run (m := EStateM Unit (EvalState (Fin 3) (List (Fin 3 × Nat)))) resetRequest (body 1)
      (recordLookup 1 0 ⟨[], []⟩) with
  | .error e state => .error e state
  | .ok result state => .ok result.value (recordComplete listOps 1 result state)

example : (match broken with | .ok value _ => some value | .error _ _ => none) = some 2 := by decide +kernel

example : (match broken with | .ok _ state => Event.completedKeys state.events | .error _ _ => []) =
    [1, 0, 0] := by decide +kernel

example : ¬ ([1, 0, 0] : List (Fin 3)).Nodup := by decide +kernel

-- The generic theorem applies without a global call/miss bound as a premise.
example : ∃ final, evalRoots listOps problem.body 3 [2, 2] ⟨[], []⟩ =
      .ok [3, 3] final ∧
    TraceInvariant listOps problem [] final ∧
    (Event.completedKeys final.events).length ≤ 3 := by
  simpa [problem, answer, listOps, ListCache.ops] using roots_expansion_bound listOps problem Finset.univ
    (by simp) 3 [2, 2] [] (by simp [listOps, ListCache.ops])
    (ListCache.initial_sound answer) (by simp [problem]) (by simp)

end MemoTests

namespace LVMemoTests

open SubtreeProofs.Paper2004.OrderedTree
open SubtreeProofs.Complexity.Memo
open SubtreeProofs.Complexity.Paper2004

private def one : DyckWord := (0 : DyckWord).nest

private def observe (result : EStateM.Result Unit (EvalState MemoKey MemoTable) Nat) :
    Option (Nat × Nat × Nat × Nat) :=
  match result with
  | .error _ _ => none
  | .ok value final => some (value, Event.calls final.events,
      (Event.completedKeys final.events).length, Event.lookupWork final.events)

example : observe (eval listOps body 1 (0, 0) ⟨[], []⟩) = some (0, 1, 1, 0) := by decide +kernel

example : observe (eval listOps body 0 (0, 0) ⟨[((0, 0), 0)], []⟩) = some (0, 1, 0, 1) := by
  decide +kernel

-- All four actual child requests survive, including the repeated empty pair.
example : observe (eval listOps body 3 (one, one) ⟨[], []⟩) = some (1, 5, 4, 4) := by
  decide +kernel

example : let run := memoLcs one one []
    (run.value, run.calls, run.misses, run.comparisons) = (1, 5, 4, 4) := by decide +kernel

-- The strong operational equality does not falsely assume a warm hit is sound.
example : observe (eval listOps body 3 (one, one) ⟨[((one, one), 17), ((one, one), 99)], []⟩) =
    some (17, 1, 0, 1) := by decide +kernel

example : (memoLcs one one []).calls ≤ 4 * (memoLcs one one []).misses + 1 :=
  memoLcs_calls_from_generic one one [] (by simp) (by intro _ hm; simp at hm)

end LVMemoTests
