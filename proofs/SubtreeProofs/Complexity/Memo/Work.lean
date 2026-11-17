module

public import SubtreeProofs.Complexity.Memo.Bounds

/-! Local representation contracts lifted to actual complete memo runs.
The size measure controls primitive budgets; it need not denote live space.
All costs here are the evaluator's declared event currencies. Source/input
operations outside those currencies still require their own realization. -/

@[expose] public section

open scoped Lean.Order
open Std.WP

namespace SubtreeProofs.Complexity.Memo

/-- Only primitive bounds and one-insertion size growth are fields. Neither
a total work bound nor a global cache-miss bound is assumed. -/
structure WorkModel (ops : CacheOps Key Value Storage) where
  size : Storage → Nat
  readCost : Nat → Nat
  writeCost : Nat → Nat
  read_mono : Monotone readCost
  write_mono : Monotone writeCost
  read_le : ∀ key storage, ops.Valid storage → (ops.read key storage).2 ≤ readCost (size storage)
  write_le : ∀ key value storage, ops.Valid storage → ops.contents storage key = none →
    (ops.write key value storage).2 ≤ writeCost (size storage)
  size_write_le : ∀ key value storage, ops.Valid storage → ops.contents storage key = none →
    size (ops.write key value storage).1 ≤ size storage + 1

/-- Bounds for actual emitted primitive work evolve with actual completions.
Past events remain covered when the upper size envelope increases. -/
structure WorkInvariant {ops : CacheOps Key Value Storage} (model : WorkModel ops)
    (origin : Storage) (state : EvalState Key Storage) : Prop where
  size_le : model.size state.cache ≤ model.size origin + (Event.completedKeys state.events).length
  reads : ∀ key work, Event.lookup key work ∈ state.events →
    work ≤ model.readCost (model.size origin + (Event.completedKeys state.events).length)
  writes : ∀ key requests localUnits work, Event.complete key requests localUnits work ∈ state.events →
    work ≤ model.writeCost (model.size origin + (Event.completedKeys state.events).length)

namespace WorkInvariant

theorem initial {ops : CacheOps Key Value Storage} (model : WorkModel ops) (origin : Storage) :
    WorkInvariant model origin ⟨origin, []⟩ := by
  refine ⟨by simp [Event.completedKeys], ?_, ?_⟩
  · intro key work hm; simp at hm
  · intro key requests localUnits work hm; simp at hm

theorem lookup {ops : CacheOps Key Value Storage} {model : WorkModel ops}
    {origin : Storage} {state : EvalState Key Storage}
    (h : WorkInvariant model origin state) (key : Key) (hv : ops.Valid state.cache) :
    WorkInvariant model origin (recordLookup key (ops.read key state.cache).2 state) := by
  refine ⟨h.size_le, ?_, ?_⟩
  · intro stored work hm
    rcases List.mem_cons.mp hm with he | hm
    · cases he
      exact Nat.le_trans (model.read_le key state.cache hv) (model.read_mono h.size_le)
    · exact h.reads stored work hm
  · intro stored requests localUnits work hm
    simp only [recordLookup, List.mem_cons, reduceCtorEq, false_or] at hm
    exact h.writes stored requests localUnits work hm

theorem complete {ops : CacheOps Key Value Storage} {model : WorkModel ops}
    {origin : Storage} {state : EvalState Key Storage}
    (h : WorkInvariant model origin state) (key : Key) (result : BodyResult Key Value)
    (hv : ops.Valid state.cache) (hf : ops.contents state.cache key = none) :
    WorkInvariant model origin (recordComplete ops key result state) := by
  have hsize := model.size_write_le key result.value state.cache hv hf
  have hprevious := h.size_le
  have hgrow : model.size origin + (Event.completedKeys state.events).length ≤
      model.size origin + ((Event.completedKeys state.events).length + 1) := by omega
  refine ⟨?_, ?_, ?_⟩
  · simp only [recordComplete, Event.completedKeys, List.length_cons]
    omega
  · intro stored work hm
    simp only [recordComplete, List.mem_cons, reduceCtorEq, false_or] at hm
    exact Nat.le_trans (h.reads stored work hm) (model.read_mono hgrow)
  · intro stored requests localUnits work hm
    simp only [recordComplete, List.mem_cons, Event.complete.injEq] at hm
    rcases hm with ⟨rfl, rfl, rfl, rfl⟩ | hm
    · exact Nat.le_trans (model.write_le stored result.value state.cache hv hf)
        (model.write_mono (Nat.le_trans h.size_le hgrow))
    · exact Nat.le_trans (h.writes stored requests localUnits work hm) (model.write_mono hgrow)

end WorkInvariant

/-- Local primitive contracts are preserved by the actual evaluator. -/
theorem roots_work_spec (ops : CacheOps Key Value Storage) (problem : Problem Key Value)
    (model : WorkModel ops) (origin : Storage) (fuel : Nat) (roots : List Key)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel) :
    ∃ final, evalRoots ops problem.body fuel roots ⟨origin, []⟩ =
        .ok (roots.map problem.value) final ∧ WorkInvariant model origin final := by
  obtain ⟨final, hr, _, _, _, hi⟩ := evalRoots_spec ops problem (WorkInvariant model origin)
    (fun key _ hi hvalid => hi.lookup key hvalid)
    (fun key result _ hi hvalid hfresh _ => hi.complete key result hvalid hfresh)
    fuel roots ⟨origin, []⟩ hv hs hbound (WorkInvariant.initial model origin)
  exact ⟨final, hr, hi⟩

theorem Event.mem_completed_of_complete {key : Key} {requests : List Key} {localUnits work : Nat}
    {events : List (Event Key)} (hm : Event.complete key requests localUnits work ∈ events) :
    key ∈ Event.completedKeys events := by
  induction events with
  | nil => simp at hm
  | cons event rest ih =>
    rcases List.mem_cons.mp hm with he | hrest
    · subst event
      exact List.mem_cons_self
    · cases event with
      | lookup _ _ => exact ih hrest
      | complete _ _ _ _ => exact List.mem_cons_of_mem _ (ih hrest)

theorem Event.lookupWork_le (events : List (Event Key)) (cap : Nat)
    (hread : ∀ key work, Event.lookup key work ∈ events → work ≤ cap) :
    Event.lookupWork events ≤ cap * Event.calls events := by
  induction events with
  | nil => simp [lookupWork, calls]
  | cons event rest ih =>
    have hr := ih (fun key work hm => hread key work (List.mem_cons_of_mem _ hm))
    cases event with
    | lookup key work =>
      have hw := hread key work List.mem_cons_self
      simp only [lookupWork, calls, Nat.mul_add, Nat.mul_one]
      omega
    | complete _ _ _ _ => exact hr

theorem Event.insertionWork_le (events : List (Event Key)) (cap : Nat)
    (hwrite : ∀ key reqs loc work, Event.complete key reqs loc work ∈ events → work ≤ cap) :
    Event.insertionWork events ≤ cap * (Event.completedKeys events).length := by
  induction events with
  | nil => simp [insertionWork, completedKeys]
  | cons event rest ih =>
    have hr := ih (fun key reqs loc work hm => hwrite key reqs loc work (List.mem_cons_of_mem _ hm))
    cases event with
    | lookup _ _ => exact hr
    | complete key reqs loc work =>
      have hw := hwrite key reqs loc work List.mem_cons_self
      simp only [insertionWork, completedKeys, List.length_cons, Nat.mul_add, Nat.mul_one]
      omega

theorem Event.localWork_eq (problem : Problem Key Value) (events : List (Event Key))
    (hb : ∀ key reqs loc ins, Event.complete key reqs loc ins ∈ events →
      loc = (Body.meaning problem.value (problem.body key)).localWork) :
    Event.localWork events = ((Event.completedKeys events).map fun key =>
      (Body.meaning problem.value (problem.body key)).localWork).sum := by
  induction events with
  | nil => rfl
  | cons event rest ih =>
    have hr := ih (fun key reqs loc ins hm => hb key reqs loc ins (List.mem_cons_of_mem _ hm))
    cases event with
    | lookup _ _ => exact hr
    | complete key reqs loc ins =>
      have he := hb key reqs loc ins List.mem_cons_self
      simp only [localWork, completedKeys, List.map_cons, List.sum_cons, he, hr]

/-- Complete declared-event work bound, retaining nonuniform request arities
and arbitrary sound warm entries outside the finite envelope. It derives all
emitted primitive budgets; no final-trace budget is supplied by the caller. -/
theorem roots_weighted_work_envelope [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (model : WorkModel ops) (envelope : Finset Key)
    (arity bodyBound : Key → Nat) (requestOverhead expansionOverhead : Nat)
    (closed : ∀ key ∈ envelope, ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → child ∈ envelope)
    (harity : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).requests.length ≤ arity key)
    (hbody : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).localWork ≤ bodyBound key)
    (fuel : Nat) (roots : List Key) (origin : Storage)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, key ∈ envelope) :
    let missing := envelope.filter fun key => (ops.contents origin key).isNone
    ∃ final, evalRoots ops problem.body fuel roots ⟨origin, []⟩ =
        .ok (roots.map problem.value) final ∧
      TraceInvariant ops problem origin final ∧
      Event.totalWork requestOverhead expansionOverhead final.events ≤
        (requestOverhead + model.readCost (model.size origin + missing.card)) *
          (roots.length + ∑ key ∈ missing, arity key) +
        (expansionOverhead + model.writeCost (model.size origin + missing.card)) * missing.card +
          ∑ key ∈ missing, bodyBound key := by
  dsimp only
  obtain ⟨final, hr, ht, hexp, hcall⟩ := roots_envelope ops problem envelope arity closed harity
    fuel roots origin hv hs hbound hroots
  obtain ⟨same, he, hw⟩ := roots_work_spec ops problem model origin fuel roots hv hs hbound
  have hsame : final = same := (EStateM.Result.ok.inj (hr.symm.trans he)).2
  rw [← hsame] at hw
  obtain ⟨insideState, he, hscope⟩ := evalRoots_scope ops problem (fun key => key ∈ envelope) closed
    fuel roots ⟨origin, []⟩ hv hs hbound hroots (by simp [Event.completedKeys])
  have hscoped : final = insideState := (EStateM.Result.ok.inj (hr.symm.trans he)).2
  rw [← hscoped] at hscope
  have hgrow := Nat.add_le_add_left hexp (model.size origin)
  let missing := envelope.filter fun key => (ops.contents origin key).isNone
  let readCap := model.readCost (model.size origin + missing.card)
  let writeCap := model.writeCost (model.size origin + missing.card)
  have hread : Event.lookupWork final.events ≤ readCap * Event.calls final.events :=
    Event.lookupWork_le final.events readCap
      (fun key work hm => Nat.le_trans (hw.reads key work hm) (model.read_mono hgrow))
  have hwrite : Event.insertionWork final.events ≤
      writeCap * (Event.completedKeys final.events).length :=
    Event.insertionWork_le final.events writeCap
      (fun key reqs loc work hm => Nat.le_trans (hw.writes key reqs loc work hm) (model.write_mono hgrow))
  have hlocal : Event.localWork final.events ≤ ∑ key ∈ missing, bodyBound key := by
    rw [Event.localWork_eq problem final.events
      (fun key reqs loc ins hm => (ht.bodies key reqs loc ins hm).2)]
    rw [← List.sum_toFinset _ ht.nodup]
    calc
      _ ≤ ∑ key ∈ (Event.completedKeys final.events).toFinset, bodyBound key :=
        Finset.sum_le_sum fun key hk => hbody key (hscope key (List.mem_toFinset.mp hk))
      _ ≤ _ := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro key hk
          have hm := List.mem_toFinset.mp hk
          exact Finset.mem_filter.mpr ⟨hscope key hm, by rw [ht.fresh key hm]; rfl⟩
        · intro key _ _; exact Nat.zero_le _
  have hwork : Event.totalWork requestOverhead expansionOverhead final.events ≤
      (requestOverhead + readCap) * Event.calls final.events +
        (expansionOverhead + writeCap) * (Event.completedKeys final.events).length +
        ∑ key ∈ missing, bodyBound key := by
    rw [Event.totalWork_eq]
    simp only [Nat.add_mul]
    omega
  refine ⟨final, hr, ht, Nat.le_trans hwork ?_⟩
  exact Nat.add_le_add_right
    (Nat.add_le_add (Nat.mul_le_mul_left _ hcall) (Nat.mul_le_mul_left _ hexp)) _

/-- Native WP contract over the same executable interpreter and proved whole-run
budget. Errors are excluded by the independent totality/descent hypotheses. -/
theorem roots_weighted_work_wp [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (model : WorkModel ops) (envelope : Finset Key)
    (arity bodyBound : Key → Nat) (requestOverhead expansionOverhead : Nat)
    (closed : ∀ key ∈ envelope, ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → child ∈ envelope)
    (harity : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).requests.length ≤ arity key)
    (hbody : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).localWork ≤ bodyBound key)
    (fuel : Nat) (roots : List Key) (origin : Storage)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, key ∈ envelope) :
    let missing := envelope.filter fun key => (ops.contents origin key).isNone
    Std.WP.wp (evalRoots ops problem.body fuel roots)
      (fun values final => values = roots.map problem.value ∧
        TraceInvariant ops problem origin final ∧
        Event.totalWork requestOverhead expansionOverhead final.events ≤
          (requestOverhead + model.readCost (model.size origin + missing.card)) *
            (roots.length + ∑ key ∈ missing, arity key) +
          (expansionOverhead + model.writeCost (model.size origin + missing.card)) * missing.card +
            ∑ key ∈ missing, bodyBound key)
      (fun _ _ => False) ⟨origin, []⟩ := by
  dsimp only
  obtain ⟨final, hr, ht, hw⟩ := roots_weighted_work_envelope ops problem model envelope arity bodyBound
    requestOverhead expansionOverhead closed harity hbody fuel roots origin hv hs hbound hroots
  simp only [Std.WP.WP.wp, Std.WP.WP.wpTrans]
  rw [hr]
  exact ⟨rfl, ht, hw⟩

/-- Uniform local body budgets specialize the nonuniform whole-run theorem. -/
theorem roots_work_envelope [DecidableEq Key] (ops : CacheOps Key Value Storage)
    (problem : Problem Key Value) (model : WorkModel ops) (envelope : Finset Key)
    (arity : Key → Nat) (bodyCap requestOverhead expansionOverhead : Nat)
    (closed : ∀ key ∈ envelope, ∀ child,
      child ∈ (Body.meaning problem.value (problem.body key)).requests → child ∈ envelope)
    (harity : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).requests.length ≤ arity key)
    (hbody : ∀ key ∈ envelope,
      (Body.meaning problem.value (problem.body key)).localWork ≤ bodyCap)
    (fuel : Nat) (roots : List Key) (origin : Storage)
    (hv : ops.Valid origin) (hs : ops.Sound problem.value origin)
    (hbound : ∀ key ∈ roots, problem.rank key < fuel)
    (hroots : ∀ key ∈ roots, key ∈ envelope) :
    let missing := envelope.filter fun key => (ops.contents origin key).isNone
    ∃ final, evalRoots ops problem.body fuel roots ⟨origin, []⟩ =
        .ok (roots.map problem.value) final ∧
      TraceInvariant ops problem origin final ∧
      Event.totalWork requestOverhead expansionOverhead final.events ≤
        (requestOverhead + model.readCost (model.size origin + missing.card)) *
          (roots.length + ∑ key ∈ missing, arity key) +
        (expansionOverhead + model.writeCost (model.size origin + missing.card) + bodyCap) *
          missing.card := by
  simpa [Nat.mul_comm, Nat.add_mul, Nat.mul_add, Nat.add_assoc] using
    roots_weighted_work_envelope ops problem model envelope arity (fun _ => bodyCap)
      requestOverhead expansionOverhead closed harity hbody fuel roots origin hv hs hbound hroots

end SubtreeProofs.Complexity.Memo
