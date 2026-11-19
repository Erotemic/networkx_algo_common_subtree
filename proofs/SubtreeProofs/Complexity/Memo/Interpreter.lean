module

public import SubtreeProofs.Complexity.Memo.Body
public import Mathlib.Data.List.MinMax

/-!
# Native sequential memo evaluation

Lookup and insertion return their own declared-model work counters. Cache
representation laws are separate from the independent value specification.
The event log records actual lookups and completed bodies, including repeated
requests. These are C1 interpreter/resource contracts; source primitives and
full source/runtime adequacy require their own realization theorems.
-/

@[expose] public section

open scoped Lean.Order
open Std.WP

namespace SubtreeProofs.Complexity.Memo

/-- A representation's actual counted operations and functional laws. Reading
preserves storage. Insertion must preserve validity when its key is fresh. -/
structure CacheOps (Key Value Storage : Type) where
  contents : Storage → Key → Option Value
  Valid : Storage → Prop
  read : Key → Storage → Option Value × Nat
  write : Key → Value → Storage → Storage × Nat
  read_correct : ∀ key storage, Valid storage → (read key storage).1 = contents storage key
  write_valid : ∀ key value storage, Valid storage → contents storage key = none →
    Valid (write key value storage).1
  write_same : ∀ key value storage, Valid storage →
    contents (write key value storage).1 key = some value
  write_other : ∀ key value storage other, Valid storage → other ≠ key →
    contents (write key value storage).1 other = contents storage other

namespace CacheOps

def Sound (ops : CacheOps Key Value Storage) (answer : Key → Value) (storage : Storage) : Prop :=
  ∀ key value, ops.contents storage key = some value → value = answer key

def Extends (ops : CacheOps Key Value Storage) (before after : Storage) : Prop :=
  ∀ key value, ops.contents before key = some value → ops.contents after key = some value

theorem Extends.refl (ops : CacheOps Key Value Storage) (storage : Storage) :
    ops.Extends storage storage := fun _ _ h => h

theorem Extends.trans {ops : CacheOps Key Value Storage} {first middle last : Storage}
    (hm : ops.Extends first middle) (hl : ops.Extends middle last) : ops.Extends first last :=
  fun key value h => hl key value (hm key value h)

theorem write_extends (ops : CacheOps Key Value Storage) (key : Key) (value : Value)
    (storage : Storage) (hv : ops.Valid storage) (hf : ops.contents storage key = none) :
    ops.Extends storage (ops.write key value storage).1 := by
  intro other old ho
  by_cases he : other = key
  · subst other
    rw [hf] at ho
    cases ho
  · rw [ops.write_other key value storage other hv he]
    exact ho

theorem write_sound (ops : CacheOps Key Value Storage) (answer : Key → Value)
    (key : Key) (value : Value) (storage : Storage) (hv : ops.Valid storage)
    (hs : ops.Sound answer storage) (hvalue : value = answer key) :
    ops.Sound answer (ops.write key value storage).1 := by
  intro other stored ho
  by_cases he : other = key
  · subst other
    rw [ops.write_same key value storage hv] at ho
    cases ho
    exact hvalue
  · rw [ops.write_other key value storage other hv he] at ho
    exact hs other stored ho

end CacheOps

/-- An independently specified recurrence, a finite request body, and a
natural descent certificate. No total runtime or cache-miss bound is a field. -/
structure Problem (Key Value : Type) where
  value : Key → Value
  body : Key → Body Key Value
  rank : Key → Nat
  body_correct : ∀ key, (Body.meaning value (body key)).value = value key
  requests_decrease : ∀ key child,
    child ∈ (Body.meaning value (body key)).requests → rank child < rank key

namespace Problem

/-- Finite direct-request lists turn any well-founded dependency relation into
a natural descent certificate. This mathematical height is not an executed
input prepass; the evaluator only receives the body and caller-supplied fuel. -/
noncomputable def requestHeight (answer : Key → Value) (body : Key → Body Key Value)
    (relation : Key → Key → Prop) (wf : WellFounded relation)
    (decreases : ∀ key child, child ∈ (Body.meaning answer (body key)).requests → relation child key) :
    Key → Nat :=
  wf.fix fun key lower =>
    1 + ((Body.meaning answer (body key)).requests.attach.map fun child =>
      lower child.val (decreases key child.val child.property)).foldr max 0

theorem requestHeight_eq (answer : Key → Value) (body : Key → Body Key Value)
    (relation : Key → Key → Prop) (wf : WellFounded relation)
    (decreases : ∀ key child, child ∈ (Body.meaning answer (body key)).requests → relation child key)
    (key : Key) :
    requestHeight answer body relation wf decreases key =
      1 + ((Body.meaning answer (body key)).requests.attach.map fun child =>
        requestHeight answer body relation wf decreases child.val).foldr max 0 := by
  rw [requestHeight, WellFounded.fix_eq]

theorem requestHeight_decreases (answer : Key → Value) (body : Key → Body Key Value)
    (relation : Key → Key → Prop) (wf : WellFounded relation)
    (decreases : ∀ key child, child ∈ (Body.meaning answer (body key)).requests → relation child key)
    (key child : Key) (hc : child ∈ (Body.meaning answer (body key)).requests) :
    requestHeight answer body relation wf decreases child <
      requestHeight answer body relation wf decreases key := by
  rw [requestHeight_eq answer body relation wf decreases key]
  have hm : requestHeight answer body relation wf decreases child ∈
      ((Body.meaning answer (body key)).requests.attach.map fun item =>
        requestHeight answer body relation wf decreases item.val) :=
    List.mem_map.mpr ⟨⟨child, hc⟩, by simp, rfl⟩
  have hle := List.le_max_of_le' 0 hm (Nat.le_refl _)
  omega

/-- A well-founded client needs no pre-existing natural rank and no decidable
relation. Its independent value and local body proof remain explicit. -/
noncomputable def ofWellFounded (answer : Key → Value) (body : Key → Body Key Value)
    (relation : Key → Key → Prop) (wf : WellFounded relation)
    (correct : ∀ key, (Body.meaning answer (body key)).value = answer key)
    (decreases : ∀ key child, child ∈ (Body.meaning answer (body key)).requests → relation child key) :
    Problem Key Value where
  value := answer
  body := body
  rank := requestHeight answer body relation wf decreases
  body_correct := correct
  requests_decrease := requestHeight_decreases answer body relation wf decreases

end Problem

/-- A completion records the direct requests and local currency returned by
that actual body execution, together with the actual insertion work. -/
inductive Event (Key : Type) where
  | lookup : Key → Nat → Event Key
  | complete : Key → List Key → Nat → Nat → Event Key
  deriving Repr

/-- Events are held in reverse chronological order. They are proof metadata,
not an asserted physical-memory or instrumentation runtime budget. -/
structure EvalState (Key Storage : Type) where
  cache : Storage
  events : List (Event Key) := []

def recordLookup (key : Key) (work : Nat) (state : EvalState Key Storage) : EvalState Key Storage :=
  ⟨state.cache, .lookup key work :: state.events⟩

def recordComplete (ops : CacheOps Key Value Storage) (key : Key)
    (result : BodyResult Key Value) (state : EvalState Key Storage) : EvalState Key Storage :=
  let stored := ops.write key result.value state.cache
  ⟨stored.1, .complete key result.requests result.localWork stored.2 :: state.events⟩

/-- Hits work at any fuel. A miss needs positive fuel, and every child receives
one less nesting unit. Failure retains its partial state; no failure-cost bound
is asserted by the successful-run theorems. -/
def eval (ops : CacheOps Key Value Storage) (body : Key → Body Key Value)
    (fuel : Nat) (key : Key) : EStateM Unit (EvalState Key Storage) Value := fun state =>
  let found := ops.read key state.cache
  let queried := recordLookup key found.2 state
  match found.1 with
  | some value => .ok value queried
  | none =>
    match fuel with
    | 0 => .error () queried
    | next + 1 =>
      match Body.run (m := EStateM Unit (EvalState Key Storage)) (eval ops body next) (body key) queried with
      | .error error failed => .error error failed
      | .ok result finished =>
        .ok result.value (recordComplete ops key result finished)
termination_by fuel

/-- A root occurrence is a call even when another root has the same key.
Each root receives the cache left by its predecessor. -/
def evalRoots (ops : CacheOps Key Value Storage) (body : Key → Body Key Value) (fuel : Nat) :
    List Key → EStateM Unit (EvalState Key Storage) (List Value)
  | [] => pure []
  | key :: rest => do
    let value ← eval ops body fuel key
    let values ← evalRoots ops body fuel rest
    pure (value :: values)

/-- Functional postconditions needed by subsequent requests. The frame above
the current rank prevents a child from filling its still-absent parent key. -/
structure Post (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (key : Key) (before after : EvalState Key Storage) : Prop where
  valid : ops.Valid after.cache
  sound : ops.Sound problem.value after.cache
  monotone : ops.Extends before.cache after.cache
  above : ∀ other, problem.rank key < problem.rank other →
    ops.contents after.cache other = ops.contents before.cache other

/-- Success, independent value correctness and cache preservation follow from
local body/representation laws. Additional invariants need only survive the
actual lookup and fresh completed insertion, not arbitrary state updates. -/
theorem eval_spec (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (invariant : EvalState Key Storage → Prop)
    (lookup_preserves : ∀ key state, invariant state → ops.Valid state.cache →
      invariant (recordLookup key (ops.read key state.cache).2 state))
    (complete_preserves : ∀ key result state, invariant state → ops.Valid state.cache →
      ops.contents state.cache key = none →
      result = Body.meaning problem.value (problem.body key) →
      invariant (recordComplete ops key result state))
    (fuel : Nat) (key : Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : problem.rank key < fuel) (hinvariant : invariant state) :
    ∃ final, eval ops problem.body fuel key state = .ok (problem.value key) final ∧
      Post ops problem key state final ∧ invariant final := by
  induction fuel generalizing key state with
  | zero => omega
  | succ fuel ih =>
    let queried := recordLookup key (ops.read key state.cache).2 state
    have hqueried : invariant queried := lookup_preserves _ _ hinvariant hv
    cases hread : (ops.read key state.cache).1 with
    | some value =>
      have hvalue : value = problem.value key :=
        hs key value ((ops.read_correct key state.cache hv).symm.trans hread)
      refine ⟨queried, ?_, ⟨hv, hs, CacheOps.Extends.refl ops state.cache, fun _ _ => rfl⟩,
        hqueried⟩
      rw [eval]
      simp only [hread, hvalue]
      rfl
    | none =>
      have hmissing : ops.contents state.cache key = none :=
        (ops.read_correct key state.cache hv).symm.trans hread
      let I : EvalState Key Storage → Prop := fun current =>
        ops.Valid current.cache ∧ ops.Sound problem.value current.cache ∧
        ops.Extends state.cache current.cache ∧
        (∀ other, problem.rank key ≤ problem.rank other →
          ops.contents current.cache other = ops.contents state.cache other) ∧ invariant current
      have hI : I queried :=
        ⟨hv, hs, CacheOps.Extends.refl ops state.cache, fun _ _ => rfl, hqueried⟩
      have handler : ∀ child ∈ (Body.meaning problem.value (problem.body key)).requests,
          ∀ current, I current →
          ∃ final, eval ops problem.body fuel child current = .ok (problem.value child) final ∧ I final := by
        intro child hc current hi
        rcases hi with ⟨hvalid, hsound, hextends, hframe, hkeep⟩
        have hdecrease := problem.requests_decrease key child hc
        obtain ⟨final, hr, hp, hf⟩ := ih child current hvalid hsound (by omega) hkeep
        refine ⟨final, hr, hp.valid, hp.sound, hextends.trans hp.monotone, ?_, hf⟩
        intro other ho
        exact (hp.above other (by omega)).trans (hframe other ho)
      obtain ⟨finished, hbody, hfinished⟩ :=
        Body.run_spec problem.value (problem.body key) (eval ops problem.body fuel) I handler queried hI
      rcases hfinished with ⟨hvalid, hsound, hextends, hframe, hkeep⟩
      have hfresh : ops.contents finished.cache key = none :=
        (hframe key (Nat.le_refl _)).trans hmissing
      let result := Body.meaning problem.value (problem.body key)
      let final := recordComplete ops key result finished
      have hvalue : result.value = problem.value key := problem.body_correct key
      refine ⟨final, ?_, ?_, complete_preserves key result finished hkeep hvalid hfresh rfl⟩
      · have hbody' : Body.run (m := EStateM Unit (EvalState Key Storage))
            (eval ops problem.body fuel) (problem.body key)
            (recordLookup key (ops.read key state.cache).2 state) = .ok result finished := hbody
        rw [eval]
        simp only [hread]
        rw [hbody']
        change EStateM.Result.ok result.value final = .ok (problem.value key) final
        rw [hvalue]
      · refine ⟨ops.write_valid key result.value finished.cache hvalid hfresh,
          ops.write_sound problem.value key result.value finished.cache hvalid hsound hvalue,
          hextends.trans (ops.write_extends key result.value finished.cache hvalid hfresh), ?_⟩
        intro other ho
        have hne : other ≠ key := by intro he; subst other; omega
        change ops.contents (ops.write key result.value finished.cache).1 other = _
        rw [ops.write_other key result.value finished.cache other hvalid hne]
        exact hframe other (by omega)

theorem eval_correct (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (fuel : Nat) (key : Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : problem.rank key < fuel) :
    ∃ final, eval ops problem.body fuel key state = .ok (problem.value key) final ∧
      Post ops problem key state final := by
  obtain ⟨final, hr, hp, _⟩ := eval_spec ops problem (fun _ => True)
    (fun _ _ _ _ => trivial) (fun _ _ _ _ _ _ _ => trivial) fuel key state hv hs hbound trivial
  exact ⟨final, hr, hp⟩

/-- A warm hit needs no positive-fuel or descent assumption. -/
theorem eval_hit (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (fuel : Nat) (key : Key) (state : EvalState Key Storage) (value : Value)
    (hread : (ops.read key state.cache).1 = some value) :
    eval ops problem.body fuel key state =
      .ok value (recordLookup key (ops.read key state.cache).2 state) := by
  rw [eval.eq_def]
  simp only [hread]

/-- The native WP contract uses the proved execution and cache postconditions;
it does not introduce a second predicate-transformer semantics. -/
theorem eval_wp (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (fuel : Nat) (key : Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : problem.rank key < fuel) :
    Std.WP.wp (eval ops problem.body fuel key)
      (fun value final => value = problem.value key ∧ Post ops problem key state final)
      (fun _ _ => False) state := by
  obtain ⟨final, hr, hp⟩ := eval_correct ops problem fuel key state hv hs hbound
  simp only [Std.WP.WP.wp, Std.WP.WP.wpTrans]
  rw [hr]
  exact ⟨rfl, hp⟩

/-- Multi-root correctness preserves input order, multiplicity, warm cache
contents and the caller's invariant through the actual sequential execution. -/
theorem evalRoots_spec (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (invariant : EvalState Key Storage → Prop)
    (lookup_preserves : ∀ key state, invariant state → ops.Valid state.cache →
      invariant (recordLookup key (ops.read key state.cache).2 state))
    (complete_preserves : ∀ key result state, invariant state → ops.Valid state.cache →
      ops.contents state.cache key = none →
      result = Body.meaning problem.value (problem.body key) →
      invariant (recordComplete ops key result state))
    (fuel : Nat) (roots : List Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel) (hinvariant : invariant state) :
    ∃ final, evalRoots ops problem.body fuel roots state = .ok (roots.map problem.value) final ∧
      ops.Valid final.cache ∧ ops.Sound problem.value final.cache ∧
      ops.Extends state.cache final.cache ∧ invariant final := by
  induction roots generalizing state with
  | nil => exact ⟨state, rfl, hv, hs, CacheOps.Extends.refl ops state.cache, hinvariant⟩
  | cons key rest ih =>
    obtain ⟨middle, hfirst, hp, hm⟩ :=
      eval_spec ops problem invariant lookup_preserves complete_preserves fuel key state hv hs
        (hbound key List.mem_cons_self) hinvariant
    obtain ⟨final, hrest, hvalid, hsound, hextends, hf⟩ :=
      ih middle hp.valid hp.sound (fun child hc => hbound child (List.mem_cons_of_mem key hc)) hm
    refine ⟨final, ?_, hvalid, hsound, hp.monotone.trans hextends, hf⟩
    simp [evalRoots, bind, EStateM.bind, pure, EStateM.pure, hfirst, hrest]

end SubtreeProofs.Complexity.Memo
