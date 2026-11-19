module

public import SubtreeProofs.Rust.SourcePairInsertSetup
public import SubtreeProofs.Rust.SourceEmptyEmbeddingViews

/-! Construct the actual selected-witness address and its reborrow. Older loan
origins are retained independently of the two fresh native embedding views.
The resulting mixed loan guard permits insertion to move its table argument. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_insert_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active)
    (callee : Derived.Callees) (result : CommonEmbedding)
    (selected : active.state 99 = Slot.ofValue (encodeResult result))
    (outside108 : 108 ∉ exceptions) (outside109 : 109 ∉ exceptions)
    {root108 root109 : Binding} (bound108 : active.roots 108 = some root108) (bound109 : active.roots 109 = some root109)
    (empty108 : active.state 108 = .empty) (empty109 : active.state 109 = .empty)
    (raw108 : world.memory[root108.address]? = some (.node .tuple 0 []))
    (raw109 : world.memory[root109.address]? = some (.node .tuple 0 []))
    (heldAbove : ∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length world active slot) :
    ∃ final after,
      Calling.Prefix callee callers (finishCode 32) ((finishActions.drop 30).take 2) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 108 = .shared (encodeResult result) ∧ after.state 109 = .shared (encodeResult result) ∧
      (∀ slot ∈ exceptions, LoanOrigin final after before.memory.length slot) ∧
      (∀ slot ∈ exceptions, (after.state slot).dropWork.boxes = 0) ∧
      ClosedOutside (108 :: 109 :: exceptions) after.state ∧ MemoLoanOrigins before.memory.length final after ∧
      (∀ slot ∈ [71, 85, 99], LocalOwnersAbove before.memory.length final after slot) ∧
      (∀ slot ∈ [106, 107], after.state slot = active.state slot) ∧
      (∀ slot, slot ≠ 108 → slot ≠ 109 →
        (∀ value, active.state slot ≠ .shared value) → after.state slot = active.state slot) ∧
      (∀ slot binding, slot ≠ 108 → slot ≠ 109 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let p30 := active.forgetRefs (finishCode 30)
  have m30 := h.prepare (finishCode 30)
  have selected30 : p30.state 99 = Slot.ofValue (encodeResult result) :=
    (LoanEnding.forget_closed (finishCode 30) _ (by rw [selected]; exact ofValue_typed (result_typed result)) (.adt .embedding)).trans selected
  have safeReference : LoanSafe (Slot.ofValue (.reference (encodeResult result))) := by
    simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.result result)
  obtain ⟨cell109, assign109, m109⟩ := m30.native.assign_empty bound109 raw109
    (address_local_source (state := p30.state) (slot := 99) (value := encodeResult result)
      (by rw [selected30]; exact Slot.materialize_ofValue _))
    (LoanEnding.forget_empty _ _ empty109) m30.native.safe safeReference (by intros; trivial)
  simp only [Slot.ofValue] at assign109 m109
  let w109 := world.write root109.address cell109
  let a109 : Activation := {p30 with state := p30.state.set 109 (.shared (encodeResult result))}
  change LoanSafeMachine before callers previous external w109 a109 at m109
  have origins109 : ∀ slot ∈ exceptions, LoanOrigin w109 a109 before.memory.length slot := by
    intro slot member
    have different : slot ≠ 109 := by intro same; subst slot; exact outside109 member
    exact ((m30.origins slot member).write_other m30.native.valid bound109 different (m30.zero slot member)
      (m30.native.fresh 109 root109 bound109) cell109).congr (after := a109) rfl rfl
        (by simp only [a109, p30, Partial.Locals.set, different, ite_false])
  have zero109 : ∀ slot ∈ exceptions, (a109.state slot).dropWork.boxes = 0 := by
    intro slot member
    have different : slot ≠ 109 := by intro same; subst slot; exact outside109 member
    simpa only [a109, Partial.Locals.set, different, ite_false] using m30.zero slot member
  have raw108a := Activation.write_other_root m30.native.valid bound109 bound108 (by decide) raw108 cell109
  let p31 := a109.forgetRefs (finishCode 31)
  have m31 := m109.prepare (finishCode 31)
  have value109 : p31.state 109 = .shared (encodeResult result) := by
    rw [Activation.forgetRefs_observed a109 (finishCode 31) 109 (by decide +kernel)]
    simp only [a109, Partial.Locals.set, ite_true]
  have empty108p : p31.state 108 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a109, Partial.Locals.set, show (108 : Nat) ≠ 109 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty108
  obtain ⟨cell108, assign108, machine⟩ := m31.assign_empty bound108 raw108a (address_shared_source value109)
    empty108p m31.safe safeReference (by intros; trivial)
  simp only [Slot.ofValue] at assign108 machine
  let final := w109.write root108.address cell108
  let after : Activation := {p31 with state := p31.state.set 108 (.shared (encodeResult result))}
  change LoanSafeMachine before callers previous external final after at machine
  have whole : Calling.Prefix callee callers (finishCode 32) ((finishActions.drop 30).take 2) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 109 (.address (.local 99))) assign109)
      (.cons (Calling.instruction_noncall_run (act := .assign 108 (.address (.deref (.local 109)))) assign108) (.nil _ _))
  have origins : ∀ slot ∈ exceptions, LoanOrigin final after before.memory.length slot := by
    intro slot member
    have different : slot ≠ 108 := by intro same; subst slot; exact outside108 member
    have zero : (p31.state slot).dropWork.boxes = 0 :=
      (Activation.forgetRefs_boxes a109 (finishCode 31) slot).trans (zero109 slot member)
    exact (((origins109 slot member).prepare (finishCode 31)).write_other m31.valid bound108 different zero
      (m31.fresh 108 root108 bound108) cell108).congr (after := after) rfl rfl
        (by simp only [after, p31, Partial.Locals.set, different, ite_false])
  have zeros : ∀ slot ∈ exceptions, (after.state slot).dropWork.boxes = 0 := by
    intro slot member
    have different : slot ≠ 108 := by intro same; subst slot; exact outside108 member
    simpa only [after, Partial.Locals.set, different, ite_false] using
      (Activation.forgetRefs_boxes a109 (finishCode 31) slot).trans (zero109 slot member)
  have wide : ClosedOutside (108 :: 109 :: exceptions) active.state :=
    h.closed.enlarge (by intro slot member; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ member))
  have closed : ClosedOutside (108 :: 109 :: exceptions) after.state :=
    (((wide.forget (finishCode 30) _).set_exception (by simp) (.shared (encodeResult result))).forget (finishCode 31) _).set_exception (by simp) _
  have value108 : after.state 108 = .shared (encodeResult result) := by simp only [after, Partial.Locals.set, ite_true]
  have final109 : after.state 109 = .shared (encodeResult result) := by
    simpa only [after, Partial.Locals.set, show (109 : Nat) ≠ 108 by decide, ite_false] using value109
  have mixed : MemoLoanOrigins before.memory.length final after := by
    intro slot
    by_cases original : slot ∈ exceptions
    · exact .inl (origins slot original)
    · apply Or.inr
      by_cases same108 : slot = 108
      · subst slot; rw [value108]; exact .shared (.result result)
      · by_cases same109 : slot = 109
        · subst slot; rw [final109]; exact .shared (.result result)
        · obtain ⟨ty, typed, shape⟩ := closed slot (by simpa using And.intro same108 (And.intro same109 original))
          exact MemoLoans.of_closed typed shape
  refine ⟨final, after, whole, machine, rfl, rfl, rfl, value108, final109, origins, zeros, closed, mixed, ?_, ?_, ?_, ?_⟩
  · intro slot member
    exact whole.owner_transfer (OwnerTransfer.kept (by decide +kernel) (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl <;> decide +kernel)) h.native.valid h.native.callersValid h.native.wellFormed (heldAbove slot member)
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> exact whole.retained_local_same_calls (by decide +kernel) (by decide +kernel)
  · intro slot other108 other109 unshared
    exact whole.unshared_local_same h.native.valid h.native.callersValid h.native.wellFormed unshared (by decide +kernel)
      (by simp [finishActions, LocalPreservation.action, LocalPreservation.expression, other108, other109])
  · intro slot binding other108 other109 root raw read
    have rootNow : p31.roots slot = some binding := root
    exact Activation.write_other_root m31.valid bound108 rootNow (Ne.symm other108)
      (Activation.write_other_root m30.native.valid bound109 root (Ne.symm other109) read cell109) cell108

end SubtreeProofs.Rust.SourceEval.Evaluator
