module

public import SubtreeProofs.Complexity.Memo.Interpreter
public import Mathlib.Data.Finset.Card

/-!
# Actual memo events and cache-domain accounting

The trace is emitted by the native evaluator. Completed bodies carry their
actual direct requests and local currency; lookups carry the representation's
actual declared-model counter. The following invariants concern execution,
not a list of states supplied independently of the interpreter.
-/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo

namespace Event

def completedKeys : List (Event Key) → List Key
  | [] => []
  | .lookup _ _ :: rest => completedKeys rest
  | .complete key _ _ _ :: rest => key :: completedKeys rest

def calls : List (Event Key) → Nat
  | [] => 0
  | .lookup _ _ :: rest => calls rest + 1
  | .complete _ _ _ _ :: rest => calls rest

def bodyRequests : List (Event Key) → Nat
  | [] => 0
  | .lookup _ _ :: rest => bodyRequests rest
  | .complete _ requests _ _ :: rest => requests.length + bodyRequests rest

def lookupWork : List (Event Key) → Nat
  | [] => 0
  | .lookup _ work :: rest => work + lookupWork rest
  | .complete _ _ _ _ :: rest => lookupWork rest

def insertionWork : List (Event Key) → Nat
  | [] => 0
  | .lookup _ _ :: rest => insertionWork rest
  | .complete _ _ _ work :: rest => work + insertionWork rest

def localWork : List (Event Key) → Nat
  | [] => 0
  | .lookup _ _ :: rest => localWork rest
  | .complete _ _ work _ :: rest => work + localWork rest

/-- Prices include any chosen interpreter overhead once per actual lookup or
completed expansion. The representation counters retain their own currency. -/
def work (requestOverhead expansionOverhead : Nat) : Event Key → Nat
  | .lookup _ work => requestOverhead + work
  | .complete _ _ localUnits insertion => expansionOverhead + localUnits + insertion

def totalWork (requestOverhead expansionOverhead : Nat) (events : List (Event Key)) : Nat :=
  (events.map (work requestOverhead expansionOverhead)).sum

theorem totalWork_eq (requestOverhead expansionOverhead : Nat) (events : List (Event Key)) :
    totalWork requestOverhead expansionOverhead events =
      requestOverhead * calls events + expansionOverhead * (completedKeys events).length +
        lookupWork events + insertionWork events + localWork events := by
  induction events with
  | nil => simp [totalWork, calls, completedKeys, lookupWork, insertionWork, localWork]
  | cons event rest ih =>
    cases event <;>
      simp [totalWork, work, calls, completedKeys, lookupWork, insertionWork, localWork,
        Nat.mul_succ] at * <;> omega

end Event

/-- Completed keys are distinct, initially absent and still live. Coverage
also records that the evaluator introduces no unlogged cache entry. -/
structure TraceInvariant (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (origin : Storage) (state : EvalState Key Storage) : Prop where
  nodup : (Event.completedKeys state.events).Nodup
  live : ∀ key ∈ Event.completedKeys state.events, ∃ value, ops.contents state.cache key = some value
  fresh : ∀ key ∈ Event.completedKeys state.events, ops.contents origin key = none
  original : ops.Extends origin state.cache
  coverage : ∀ key value, ops.contents state.cache key = some value →
    ops.contents origin key = some value ∨ key ∈ Event.completedKeys state.events
  bodies : ∀ key requests localUnits insertion,
    Event.complete key requests localUnits insertion ∈ state.events →
      requests = (Body.meaning problem.value (problem.body key)).requests ∧
      localUnits = (Body.meaning problem.value (problem.body key)).localWork

namespace TraceInvariant

theorem initial (ops : CacheOps Key Value Storage) (problem : Problem Key Value) (origin : Storage) :
    TraceInvariant ops problem origin ⟨origin, []⟩ := by
  refine ⟨by simp [Event.completedKeys], ?_, ?_, CacheOps.Extends.refl ops origin, ?_, ?_⟩
  · intro key hk; simp [Event.completedKeys] at hk
  · intro key hk; simp [Event.completedKeys] at hk
  · intro key value hk; exact Or.inl hk
  · intro key requests localUnits insertion he; simp at he

theorem lookup {ops : CacheOps Key Value Storage} {problem : Problem Key Value}
    {origin : Storage} {state : EvalState Key Storage}
    (h : TraceInvariant ops problem origin state) (key : Key) (work : Nat) :
    TraceInvariant ops problem origin (recordLookup key work state) := by
  refine ⟨h.nodup, h.live, h.fresh, h.original, h.coverage, ?_⟩
  intro stored requests localUnits insertion he
  simp only [recordLookup, List.mem_cons, reduceCtorEq, false_or] at he
  exact h.bodies stored requests localUnits insertion he

theorem complete {ops : CacheOps Key Value Storage} {problem : Problem Key Value}
    {origin : Storage} {state : EvalState Key Storage}
    (h : TraceInvariant ops problem origin state) (key : Key) (result : BodyResult Key Value)
    (hv : ops.Valid state.cache) (hf : ops.contents state.cache key = none)
    (hresult : result = Body.meaning problem.value (problem.body key)) :
    TraceInvariant ops problem origin (recordComplete ops key result state) := by
  have hnew : key ∉ Event.completedKeys state.events := by
    intro hk
    obtain ⟨value, he⟩ := h.live key hk
    rw [hf] at he
    cases he
  have hwrite := ops.write_extends key result.value state.cache hv hf
  have horigin : ops.contents origin key = none := by
    cases he : ops.contents origin key with
    | none => rfl
    | some value =>
      have hc := h.original key value he
      rw [hf] at hc
      cases hc
  refine ⟨List.nodup_cons.mpr ⟨hnew, h.nodup⟩, ?_, ?_, h.original.trans hwrite, ?_, ?_⟩
  · intro stored hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact ⟨result.value, ops.write_same stored result.value state.cache hv⟩
    · obtain ⟨value, he⟩ := h.live stored hs
      exact ⟨value, hwrite stored value he⟩
  · intro stored hs
    rcases List.mem_cons.mp hs with rfl | hs
    · exact horigin
    · exact h.fresh stored hs
  · intro stored value hs
    by_cases he : stored = key
    · exact Or.inr (List.mem_cons.mpr (Or.inl he))
    · change ops.contents (ops.write key result.value state.cache).1 stored = some value at hs
      rw [ops.write_other key result.value state.cache stored hv he] at hs
      rcases h.coverage stored value hs with old | fresh
      · exact Or.inl old
      · exact Or.inr (List.mem_cons_of_mem _ fresh)
  · intro stored requests localUnits insertion he
    simp only [recordComplete, List.mem_cons, Event.complete.injEq] at he
    rcases he with ⟨rfl, rfl, rfl, _⟩ | he
    · subst result
      exact ⟨rfl, rfl⟩
    · exact h.bodies stored requests localUnits insertion he

end TraceInvariant

/-- One successful evaluator call contributes one lookup beyond the direct
requests recorded by completed bodies. This holds for every successful fuel,
independently of cache soundness or the value specification. -/
theorem eval_balance (ops : CacheOps Key Value Storage) (body : Key → Body Key Value)
    (fuel : Nat) (key : Key) {state final : EvalState Key Storage} {value : Value}
    (hr : eval ops body fuel key state = .ok value final) :
    Event.calls final.events + Event.bodyRequests state.events =
      Event.calls state.events + Event.bodyRequests final.events + 1 := by
  induction fuel generalizing key state final value with
  | zero =>
    rw [eval] at hr
    cases he : (ops.read key state.cache).1 with
    | none => simp [he] at hr
    | some stored =>
      simp only [he, EStateM.Result.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [recordLookup, Event.calls, Event.bodyRequests]
      omega
  | succ fuel ih =>
    rw [eval] at hr
    cases he : (ops.read key state.cache).1 with
    | some stored =>
      simp only [he, EStateM.Result.ok.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      simp only [recordLookup, Event.calls, Event.bodyRequests]
      omega
    | none =>
      simp only [he] at hr
      cases hb : Body.run (m := EStateM Unit (EvalState Key Storage)) (eval ops body fuel)
          (body key) (recordLookup key (ops.read key state.cache).2 state) with
      | error error failed => simp [hb] at hr
      | ok result finished =>
        have hbalance := Body.run_balance (body key) (eval ops body fuel)
          (fun current => Event.calls current.events) (fun current => Event.bodyRequests current.events)
          (fun child _ _ _ hchild => ih child hchild) hb
        simp only [hb, EStateM.Result.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        simp only [recordLookup, recordComplete, Event.calls, Event.bodyRequests] at *
        omega

theorem evalRoots_balance (ops : CacheOps Key Value Storage) (body : Key → Body Key Value)
    (fuel : Nat) (roots : List Key) {state final : EvalState Key Storage} {values : List Value}
    (hr : evalRoots ops body fuel roots state = .ok values final) :
    Event.calls final.events + Event.bodyRequests state.events =
      Event.calls state.events + Event.bodyRequests final.events + roots.length := by
  induction roots generalizing state final values with
  | nil =>
    simp only [evalRoots, pure, EStateM.pure, EStateM.Result.ok.injEq] at hr
    obtain ⟨rfl, rfl⟩ := hr
    simp
  | cons key rest ih =>
    cases he : eval ops body fuel key state with
    | error error failed => simp [evalRoots, bind, EStateM.bind, he] at hr
    | ok first middle =>
      have hfirst := eval_balance ops body fuel key he
      cases ht : evalRoots ops body fuel rest middle with
      | error error failed => simp [evalRoots, bind, EStateM.bind, he, ht] at hr
      | ok remaining last =>
        have hrest := ih ht
        simp only [evalRoots, bind, EStateM.bind, he, ht, pure, EStateM.pure,
          EStateM.Result.ok.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        simp only [List.length_cons]
        omega

/-- The invariant is preserved by actual root evaluation, not assumed as an
unexplained fact about its final trace. -/
theorem eval_trace_spec (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (origin : Storage) (fuel : Nat) (key : Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : problem.rank key < fuel) (ht : TraceInvariant ops problem origin state) :
    ∃ final, eval ops problem.body fuel key state = .ok (problem.value key) final ∧
      Post ops problem key state final ∧ TraceInvariant ops problem origin final :=
  eval_spec ops problem (TraceInvariant ops problem origin)
    (fun key state hi _ => hi.lookup key (ops.read key state.cache).2)
    (fun key result _ hi hvalid hfresh hr => hi.complete key result hvalid hfresh hr)
    fuel key state hv hs hbound ht

/-- Exact cache-domain accounting permits unrelated initial entries outside
any later reachable-state envelope. -/
theorem TraceInvariant.domain_eq {ops : CacheOps Key Value Storage} {problem : Problem Key Value}
    {origin : Storage} {state : EvalState Key Storage}
    (h : TraceInvariant ops problem origin state) (key : Key) :
    (∃ value, ops.contents state.cache key = some value) ↔
      (∃ value, ops.contents origin key = some value) ∨ key ∈ Event.completedKeys state.events := by
  constructor
  · rintro ⟨value, hv⟩
    rcases h.coverage key value hv with old | fresh
    · exact Or.inl ⟨value, old⟩
    · exact Or.inr fresh
  · rintro (⟨value, old⟩ | fresh)
    · exact ⟨value, h.original key value old⟩
    · exact h.live key fresh

theorem TraceInvariant.mem_completed_iff {ops : CacheOps Key Value Storage}
    {problem : Problem Key Value} {origin : Storage} {state : EvalState Key Storage}
    (h : TraceInvariant ops problem origin state) (key : Key) :
    key ∈ Event.completedKeys state.events ↔
      (∃ value, ops.contents state.cache key = some value) ∧ ops.contents origin key = none := by
  constructor
  · intro hk; exact ⟨h.live key hk, h.fresh key hk⟩
  · rintro ⟨⟨value, hv⟩, hf⟩
    rcases h.coverage key value hv with old | fresh
    · rw [hf] at old; cases old
    · exact fresh

/-- Multiple roots, duplicates and warm starts all preserve once-only expansion
and exact cache-domain accounting. -/
theorem evalRoots_trace_spec (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (origin : Storage) (fuel : Nat) (roots : List Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (ht : TraceInvariant ops problem origin state) :
    ∃ final, evalRoots ops problem.body fuel roots state = .ok (roots.map problem.value) final ∧
      ops.Valid final.cache ∧ ops.Sound problem.value final.cache ∧
      ops.Extends state.cache final.cache ∧ TraceInvariant ops problem origin final :=
  evalRoots_spec ops problem (TraceInvariant ops problem origin)
    (fun key state hi _ => hi.lookup key (ops.read key state.cache).2)
    (fun key result _ hi hvalid hfresh hr => hi.complete key result hvalid hfresh hr)
    fuel roots state hv hs hbound ht

end SubtreeProofs.Complexity.Memo
