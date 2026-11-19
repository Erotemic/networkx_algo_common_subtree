module

public import SubtreeProofs.Complexity.Memo.Trace
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! Exact successful-run request counts and finite, warm-cache envelopes.
The envelope is closed under the independent body's requests; membership of
actual completed keys is proved from execution. No total work bound is a
problem or representation field. -/

@[expose] public section

namespace SubtreeProofs.Complexity.Memo

open scoped BigOperators

theorem Event.bodyRequests_eq (problem : Problem Key Value) (events : List (Event Key))
    (hb : ∀ key requests localUnits insertion,
      Event.complete key requests localUnits insertion ∈ events →
      requests = (Body.meaning problem.value (problem.body key)).requests) :
    Event.bodyRequests events =
      ((Event.completedKeys events).map fun key =>
        (Body.meaning problem.value (problem.body key)).requests.length).sum := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have hr := ih (fun key reqs loc ins hm => hb key reqs loc ins (List.mem_cons_of_mem _ hm))
    cases event with
    | lookup key work => exact hr
    | complete key reqs loc ins =>
      have he := hb key reqs loc ins List.mem_cons_self
      simp only [Event.bodyRequests, Event.completedKeys, List.map_cons, List.sum_cons, he, hr]

/-- The `+ roots.length` term retains repeated roots, including warm hits. -/
theorem roots_request_identity [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (fuel : Nat) (roots : List Key) (origin : Storage)
    {final : EvalState Key Storage} {values : List Value}
    (hr : evalRoots ops problem.body fuel roots ⟨origin, []⟩ = .ok values final)
    (ht : TraceInvariant ops problem origin final) :
    Event.calls final.events = roots.length +
      ∑ key ∈ (Event.completedKeys final.events).toFinset,
        (Body.meaning problem.value (problem.body key)).requests.length := by
  have hbalance := evalRoots_balance ops problem.body fuel roots hr
  have hb := Event.bodyRequests_eq problem final.events
    (fun key reqs loc ins hm => (ht.bodies key reqs loc ins hm).1)
  rw [List.sum_toFinset _ ht.nodup]
  simp only [Event.bodyRequests, Event.calls] at hbalance
  omega

/-- Closure of canonical requests suffices even for value-dependent bodies:
sound caches force the actual continuation to use the independent values. -/
theorem eval_scope (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (scope : Key → Prop)
    (closed : ∀ key, scope key → ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → scope child)
    (fuel : Nat) (key : Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : problem.rank key < fuel) (hk : scope key)
    (hi : ∀ stored ∈ Event.completedKeys state.events, scope stored) :
    ∃ final, eval ops problem.body fuel key state = .ok (problem.value key) final ∧
      (∀ stored ∈ Event.completedKeys final.events, scope stored) := by
  induction fuel generalizing key state with
  | zero => omega
  | succ fuel ih =>
    cases hread : (ops.read key state.cache).1 with
    | some value =>
      have hvalue := hs key value ((ops.read_correct key state.cache hv).symm.trans hread)
      refine ⟨recordLookup key (ops.read key state.cache).2 state, ?_, hi⟩
      rw [eval]
      simp only [hread, hvalue]
    | none =>
      let I : EvalState Key Storage → Prop := fun current =>
        ops.Valid current.cache ∧ ops.Sound problem.value current.cache ∧
        ∀ stored ∈ Event.completedKeys current.events, scope stored
      have handler : ∀ child ∈ (Body.meaning problem.value (problem.body key)).requests,
          ∀ current, I current →
          ∃ final, eval ops problem.body fuel child current = .ok (problem.value child) final ∧
            I final := by
        intro child hc current ⟨hvalid, hsound, hscope⟩
        have hd := problem.requests_decrease key child hc
        obtain ⟨final, hr, hf⟩ := ih child current hvalid hsound (by omega)
          (closed key hk child hc) hscope
        obtain ⟨same, he, hp⟩ := eval_correct ops problem fuel child current hvalid hsound (by omega)
        rw [hr] at he
        cases he
        exact ⟨final, hr, hp.valid, hp.sound, hf⟩
      obtain ⟨finished, hb, hf⟩ := Body.run_spec problem.value (problem.body key)
        (eval ops problem.body fuel) I handler
        (recordLookup key (ops.read key state.cache).2 state) ⟨hv, hs, hi⟩
      let result := Body.meaning problem.value (problem.body key)
      refine ⟨recordComplete ops key result finished, ?_, ?_⟩
      · have hb' : Body.run (m := EStateM Unit (EvalState Key Storage))
            (eval ops problem.body fuel) (problem.body key)
            (recordLookup key (ops.read key state.cache).2 state) = .ok result finished := hb
        rw [eval]
        simp only [hread]
        rw [hb']
        change EStateM.Result.ok result.value _ = .ok (problem.value key) _
        rw [problem.body_correct]
      · intro stored hm
        rcases List.mem_cons.mp hm with rfl | hm
        · exact hk
        · exact hf.2.2 stored hm

theorem evalRoots_scope (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (scope : Key → Prop)
    (closed : ∀ key, scope key → ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → scope child)
    (fuel : Nat) (roots : List Key) (state : EvalState Key Storage)
    (hv : ops.Valid state.cache) (hs : ops.Sound problem.value state.cache)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, scope key)
    (hi : ∀ stored ∈ Event.completedKeys state.events, scope stored) :
    ∃ final, evalRoots ops problem.body fuel roots state = .ok (roots.map problem.value) final ∧
      (∀ stored ∈ Event.completedKeys final.events, scope stored) := by
  induction roots generalizing state with
  | nil => exact ⟨state, rfl, hi⟩
  | cons key rest ih =>
    obtain ⟨middle, hr, hm⟩ := eval_scope ops problem scope closed fuel key state hv hs
      (hbound key List.mem_cons_self) (hroots key List.mem_cons_self) hi
    obtain ⟨same, he, hp⟩ := eval_correct ops problem fuel key state hv hs
      (hbound key List.mem_cons_self)
    rw [hr] at he
    cases he
    obtain ⟨final, ht, hf⟩ := ih middle hp.valid hp.sound
      (fun child hc => hbound child (List.mem_cons_of_mem _ hc))
      (fun child hc => hroots child (List.mem_cons_of_mem _ hc)) hm
    refine ⟨final, ?_, hf⟩
    simp [evalRoots, bind, EStateM.bind, pure, EStateM.pure, hr, ht]

/-- Warm entries anywhere in the key type are permitted. Only initially absent
keys inside the finite closed envelope can be completed by these roots. -/
theorem roots_expansion_bound [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (envelope : Finset Key)
    (closed : ∀ key ∈ envelope, ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → child ∈ envelope)
    (fuel : Nat) (roots : List Key) (origin : Storage)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, key ∈ envelope) :
    ∃ final, evalRoots ops problem.body fuel roots ⟨origin, []⟩ =
        .ok (roots.map problem.value) final ∧
      TraceInvariant ops problem origin final ∧
      (Event.completedKeys final.events).length ≤
        (envelope.filter fun key => (ops.contents origin key).isNone).card := by
  obtain ⟨final, hr, _, _, _, ht⟩ := evalRoots_trace_spec ops problem origin fuel roots
    ⟨origin, []⟩ hv hs hbound (TraceInvariant.initial ops problem origin)
  obtain ⟨same, he, hscope⟩ := evalRoots_scope ops problem (fun key => key ∈ envelope)
    closed fuel roots ⟨origin, []⟩ hv hs hbound hroots (by simp [Event.completedKeys])
  rw [hr] at he
  cases he
  refine ⟨final, hr, ht, ?_⟩
  rw [← List.toFinset_card_of_nodup ht.nodup]
  apply Finset.card_le_card
  intro key hk
  have hm := List.mem_toFinset.mp hk
  exact Finset.mem_filter.mpr ⟨hscope key hm, by rw [ht.fresh key hm]; rfl⟩

/-- Nonuniform local arities can be summed over a closed envelope of initially
absent keys. Sound warm entries outside the envelope remain permitted. -/
theorem roots_envelope [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (envelope : Finset Key) (arity : Key → Nat)
    (closed : ∀ key ∈ envelope, ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → child ∈ envelope)
    (harity : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).requests.length ≤ arity key)
    (fuel : Nat) (roots : List Key) (origin : Storage)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, key ∈ envelope) :
    ∃ final, evalRoots ops problem.body fuel roots ⟨origin, []⟩ =
        .ok (roots.map problem.value) final ∧
      TraceInvariant ops problem origin final ∧
      (Event.completedKeys final.events).length ≤
        (envelope.filter fun key => (ops.contents origin key).isNone).card ∧
      Event.calls final.events ≤ roots.length +
        ∑ key ∈ envelope.filter (fun key => (ops.contents origin key).isNone), arity key := by
  obtain ⟨final, hr, ht, hexp⟩ := roots_expansion_bound ops problem envelope closed
    fuel roots origin hv hs hbound hroots
  obtain ⟨same, he, hscope⟩ := evalRoots_scope ops problem (fun key => key ∈ envelope)
    closed fuel roots ⟨origin, []⟩ hv hs hbound hroots (by simp [Event.completedKeys])
  rw [hr] at he
  cases he
  refine ⟨final, hr, ht, hexp, ?_⟩
  rw [roots_request_identity ops problem fuel roots origin hr ht]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ key ∈ (Event.completedKeys final.events).toFinset, arity key :=
      Finset.sum_le_sum fun key hk => harity key (hscope key (List.mem_toFinset.mp hk))
    _ ≤ _ := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro key hk
        have hm := List.mem_toFinset.mp hk
        exact Finset.mem_filter.mpr ⟨hscope key hm, by rw [ht.fresh key hm]; rfl⟩
      · intro key _ _; exact Nat.zero_le _

/-- A uniform local request arity gives an exact-root-constant call envelope. -/
theorem roots_call_bound [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (branching fuel : Nat) (roots : List Key) (origin : Storage)
    {final : EvalState Key Storage} {values : List Value}
    (hr : evalRoots ops problem.body fuel roots ⟨origin, []⟩ = .ok values final)
    (ht : TraceInvariant ops problem origin final)
    (hbranch : ∀ key ∈ Event.completedKeys final.events,
      (Body.meaning problem.value (problem.body key)).requests.length ≤ branching) :
    Event.calls final.events ≤ roots.length + branching * (Event.completedKeys final.events).length := by
  rw [roots_request_identity ops problem fuel roots origin hr ht]
  have hsum := Finset.sum_le_sum (s := (Event.completedKeys final.events).toFinset)
    (fun key hk => hbranch key (List.mem_toFinset.mp hk))
  simpa [List.toFinset_card_of_nodup ht.nodup, Nat.mul_comm] using
    Nat.add_le_add_left hsum roots.length

/-- A priced-event composition lemma. Its premises are local emitted primitive
budgets, not an assumed total execution bound. Applying it to a representation
still requires proving these budgets from that representation's actual runs. -/
theorem Event.totalWork_le (events : List (Event Key))
    (requestOverhead expansionOverhead readCap writeCap bodyCap : Nat)
    (hread : ∀ key work, Event.lookup key work ∈ events → work ≤ readCap)
    (hcomplete : ∀ key reqs loc ins, Event.complete key reqs loc ins ∈ events →
      ins ≤ writeCap ∧ loc ≤ bodyCap) :
    Event.totalWork requestOverhead expansionOverhead events ≤
      (requestOverhead + readCap) * Event.calls events +
        (expansionOverhead + writeCap + bodyCap) * (Event.completedKeys events).length := by
  induction events with
  | nil => simp [totalWork, calls, completedKeys]
  | cons event rest ih =>
    have hr := ih (fun key work hm => hread key work (List.mem_cons_of_mem _ hm))
      (fun key reqs loc ins hm => hcomplete key reqs loc ins (List.mem_cons_of_mem _ hm))
    cases event with
    | lookup key work =>
      have hw := hread key work List.mem_cons_self
      simp only [totalWork, List.map_cons, List.sum_cons, Event.work, calls,
        completedKeys, Nat.mul_add, Nat.mul_one] at *
      omega
    | complete key reqs loc ins =>
      obtain ⟨hw, hl⟩ := hcomplete key reqs loc ins List.mem_cons_self
      simp only [totalWork, List.map_cons, List.sum_cons, Event.work, calls,
        completedKeys, List.length_cons, Nat.mul_add, Nat.mul_one] at *
      omega

end SubtreeProofs.Complexity.Memo
