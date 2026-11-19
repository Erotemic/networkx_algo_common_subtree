module

public import Std.WP.Monad.Instances
public import Std.WP.Monad.Sound
public import Mathlib.Data.List.Basic

/-!
# Sequential bodies with memo requests

A body can request a dependency value, choose subsequent requests from that
answer, and record local work in an explicit currency. It cannot inspect or
mutate a memo cache. The interpreter uses the existing monad supplied by its
caller; this module defines no new resource monad or verification engine.

The local-work currency describes this request model. A source application
must separately justify its local primitives and body/key construction; these
rules do not give arbitrary Lean expressions or Rust operations a runtime cost.
-/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo

/-- A finite request body. Repeated requests remain separate occurrences. -/
inductive Body (Key Value : Type) where
  | done : Value → Body Key Value
  | pay : Nat → Body Key Value → Body Key Value
  | ask : Key → (Value → Body Key Value) → Body Key Value

/-- Direct requests and local work of one body execution, excluding the
recursive work performed by its request handler. -/
structure BodyResult (Key Value : Type) where
  value : Value
  requests : List Key
  localWork : Nat
  deriving Repr

namespace Body

/-- Interpret each request through the caller's handler and retain the actual
branch's direct occurrences. The body never observes the handler's state. -/
def run [Monad m] (request : Key → m Value) : Body Key Value → m (BodyResult Key Value)
  | .done value => pure ⟨value, [], 0⟩
  | .pay units rest => do
    let result ← run request rest
    pure ⟨result.value, result.requests, units + result.localWork⟩
  | .ask key next => do
    let value ← request key
    let result ← run request (next value)
    pure ⟨result.value, key :: result.requests, result.localWork⟩

/-- Erase the request/work metadata while retaining all handler effects. -/
def eval [Monad m] (request : Key → m Value) : Body Key Value → m Value
  | .done value => pure value
  | .pay _ rest => eval request rest
  | .ask key next => do
    let value ← request key
    eval request (next value)

/-- Instrumentation does not change handler effects, their order, or results.
This is monadic equality, not just equality after discarding the final state. -/
theorem erase_run [Monad m] [LawfulMonad m] (request : Key → m Value)
    (body : Body Key Value) :
    (fun result => result.value) <$> run request body = eval request body := by
  induction body with
  | done value => simp [run, eval]
  | pay units rest ih => simpa [run, eval, map_bind, Function.comp_def] using ih
  | ask key next ih => simp [run, eval, map_bind, ih]

/-- Independent body interpretation under canonical dependency answers.
It has no memo cache and does not invoke the memo evaluator. -/
def meaning (answer : Key → Value) (body : Body Key Value) : BodyResult Key Value :=
  run (m := Id) answer body

@[simp] theorem meaning_done (answer : Key → Value) (value : Value) :
    meaning answer (.done value) = ⟨value, [], 0⟩ := rfl

@[simp] theorem meaning_pay (answer : Key → Value) (units : Nat) (rest : Body Key Value) :
    meaning answer (.pay units rest) =
      ⟨(meaning answer rest).value, (meaning answer rest).requests,
        units + (meaning answer rest).localWork⟩ := rfl

@[simp] theorem meaning_ask (answer : Key → Value) (key : Key)
    (next : Value → Body Key Value) :
    meaning answer (.ask key next) =
      ⟨(meaning answer (next (answer key))).value,
        key :: (meaning answer (next (answer key))).requests,
        (meaning answer (next (answer key))).localWork⟩ := rfl

/-- Local handler contracts suffice for complete body interpretation. Only
requests on the canonical valid-response path require handler hypotheses. -/
theorem run_spec (answer : Key → Value) (body : Body Key Value)
    (request : Key → EStateM Error State Value) (invariant : State → Prop)
    (handler : ∀ key ∈ (meaning answer body).requests, ∀ state, invariant state →
      ∃ final, request key state = .ok (answer key) final ∧ invariant final)
    (state : State) (hs : invariant state) :
    ∃ final, run request body state = .ok (meaning answer body) final ∧ invariant final := by
  induction body generalizing state with
  | done value => exact ⟨state, rfl, hs⟩
  | pay units rest ih =>
    obtain ⟨final, hr, hf⟩ := ih handler state hs
    refine ⟨final, ?_, hf⟩
    simp [run, bind, EStateM.bind, pure, EStateM.pure, hr, meaning_pay]
  | ask key next ih =>
    have hk : key ∈ (meaning answer (.ask key next)).requests := by simp
    obtain ⟨middle, hreq, hm⟩ := handler key hk state hs
    have hnext : ∀ child ∈ (meaning answer (next (answer key))).requests,
        ∀ state, invariant state →
          ∃ final, request child state = .ok (answer child) final ∧ invariant final := by
      intro child hc state hi
      exact handler child (by simp [hc]) state hi
    obtain ⟨final, hr, hf⟩ := ih (answer key) hnext middle hm
    refine ⟨final, ?_, hf⟩
    simp [run, bind, EStateM.bind, pure, EStateM.pure, hreq, hr, meaning_ask]

/-- Each actual handler invocation contributes one direct request, even when
subsequent requests depend on its answer. The balance is independent of value
correctness, cache representation, and any global runtime bound. -/
theorem run_balance (body : Body Key Value) (request : Key → EStateM Error State Value)
    (calls nested : State → Nat)
    (handler : ∀ key state value final, request key state = .ok value final →
      calls final + nested state = calls state + nested final + 1)
    {state final : State} {result : BodyResult Key Value}
    (hr : run request body state = .ok result final) :
    calls final + nested state = calls state + nested final + result.requests.length := by
  induction body generalizing state final result with
  | done value =>
    simp only [run, pure, EStateM.pure, EStateM.Result.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp
  | pay units rest ih =>
    cases he : run request rest state with
    | error error failed => simp [run, bind, EStateM.bind, he] at hr
    | ok inner middle =>
      have hb := ih he
      simp only [run, bind, EStateM.bind, he, pure, EStateM.pure,
        EStateM.Result.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact hb
  | ask key next ih =>
    cases hreq : request key state with
    | error error failed => simp [run, bind, EStateM.bind, hreq] at hr
    | ok value middle =>
      have hc := handler key state value middle hreq
      cases he : run request (next value) middle with
      | error error failed => simp [run, bind, EStateM.bind, hreq, he] at hr
      | ok inner last =>
        have hb := ih value he
        simp only [run, bind, EStateM.bind, hreq, he, pure, EStateM.pure,
          EStateM.Result.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        simp only [List.length_cons]
        omega

end Body

end SubtreeProofs.Complexity.Memo
