module

public import SubtreeProofs.Rust.SourceEmptyQueryViews
public import SubtreeProofs.Rust.SourceEmbeddingLoanPermissions
public import SubtreeProofs.Rust.SourcePrefixObserved
import Mathlib.Tactic.IntervalCases

/-! Construct the actual direct embedding view and its reborrow for insertion.
The last individual query reference ends here, while the original query tuple
retains its old loan origin and the embedding views may borrow fresh witness
storage. Table-argument permission follows from their native referent shapes. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_embedding_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    (left right : BalancedWord) (closed : ClosedOutside [1, 2, 13, 20, 21] active.state)
    (tupleOrigin : LoanOrigin world active before.memory.length 13)
    (empty1 : active.state 1 = .empty) (query2 : active.state 2 = .shared (encodeWord right))
    (view20 : active.state 20 = .shared (encodeWord left)) (view21 : active.state 21 = .shared (encodeWord right))
    (tuple : active.state 13 = queryTuple left right) (witness : active.state 16 = Slot.ofValue (encodeResult emptyWitness))
    (count : 24 ≤ active.count) (unbound22 : active.roots 22 = none) (unbound23 : active.roots 23 = none) :
    ∃ (final : World) (after : Activation) (root22 root23 : Binding),
      Calling.Prefix callee callers (emptyCode 18) ((emptyActions.drop 14).take 4) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ LoanOrigin final after before.memory.length 13 ∧
      ClosedOutside [1, 2, 13, 20, 21, 22, 23] after.state ∧ MemoLoanState after.state ∧ after.count = active.count ∧
      after.roots 22 = some root22 ∧ after.roots 23 = some root23 ∧
      (∀ slot, slot ≠ 22 → slot ≠ 23 → after.roots slot = active.roots slot) ∧
      after.state 1 = .empty ∧ after.state 2 = .empty ∧ after.state 13 = queryTuple left right ∧
      after.state 20 = .shared (encodeWord left) ∧ after.state 21 = .shared (encodeWord right) ∧
      after.state 22 = .shared (encodeResult emptyWitness) ∧ after.state 23 = .shared (encodeResult emptyWitness) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let p14 := active.forgetRefs (emptyCode 14)
  have m14 := h.prepare (emptyCode 14)
  have o14 := tupleOrigin.prepare (emptyCode 14)
  have tuple14 := prepare_queryTuple tuple (emptyCode 14)
  have empty2p14 : p14.state 2 = .empty :=
    LoanEnding.forget_ended_shared (emptyCode 14) (List.range active.count) (by simp; omega) query2 (by decide +kernel)
  let root22 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w22 := world.allocate (.stack p14.frame 22 world.memory.length) (.node .tuple 0 [])
  let a22 : Activation := {p14 with roots := p14.roots.set 22 (some root22), state := p14.state.set 22 .empty}
  obtain ⟨live22, m22⟩ := m14.storageLive (slot := 22) (by change 22 < active.count; omega) unbound22
  change LoanSafeMachine before callers previous external w22 a22 at m22
  have o22 : LoanOrigin w22 a22 before.memory.length 13 :=
    (o14.allocate m14.wellFormed (.stack p14.frame 22 world.memory.length) (.node .tuple 0 [])).congr
      (after := a22) rfl (by simp only [a22, p14, Roots.set, show (13 : Nat) ≠ 22 by decide, ite_false])
      (by simp only [a22, p14, Partial.Locals.set, show (13 : Nat) ≠ 22 by decide, ite_false])
  have tuple22 : a22.state 13 = queryTuple left right := by simpa only [a22, Partial.Locals.set, show (13 : Nat) ≠ 22 by decide, ite_false] using tuple14
  have empty2a22 : a22.state 2 = .empty := by simpa only [a22, Partial.Locals.set, show (2 : Nat) ≠ 22 by decide, ite_false] using empty2p14
  let p15 := a22.forgetRefs (emptyCode 15)
  have m15 := m22.prepare (emptyCode 15)
  have o15 := o22.prepare (emptyCode 15)
  have tuple15 := prepare_queryTuple tuple22 (emptyCode 15)
  have empty2p15 : p15.state 2 = .empty := LoanEnding.forget_empty _ _ empty2a22
  let root23 : Binding := ⟨w22.memory.length, w22.memory.length⟩
  let w23 := w22.allocate (.stack p15.frame 23 w22.memory.length) (.node .tuple 0 [])
  let a23 : Activation := {p15 with roots := p15.roots.set 23 (some root23), state := p15.state.set 23 .empty}
  obtain ⟨live23, m23⟩ := m15.storageLive (slot := 23) (by change 23 < active.count; omega)
    (by simpa [p15, a22, p14, Roots.set, Activation.forgetRefs] using unbound23)
  change LoanSafeMachine before callers previous external w23 a23 at m23
  have o23 : LoanOrigin w23 a23 before.memory.length 13 :=
    (o15.allocate m15.wellFormed (.stack p15.frame 23 w22.memory.length) (.node .tuple 0 [])).congr
      (after := a23) rfl (by simp only [a23, p15, Roots.set, show (13 : Nat) ≠ 23 by decide, ite_false])
      (by simp only [a23, p15, Partial.Locals.set, show (13 : Nat) ≠ 23 by decide, ite_false])
  have tuple23 : a23.state 13 = queryTuple left right := by simpa only [a23, Partial.Locals.set, show (13 : Nat) ≠ 23 by decide, ite_false] using tuple15
  have empty2a23 : a23.state 2 = .empty := by simpa only [a23, Partial.Locals.set, show (2 : Nat) ≠ 23 by decide, ite_false] using empty2p15
  have first : Calling.Prefix callee callers (emptyCode 16) [.storageLive 22, .storageLive 23] world active w23 a23 :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 22) live22)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 23) live23) (.nil _ _))
  have witness23 : a23.state 16 = Slot.ofValue (encodeResult emptyWitness) :=
    (first.closed_local_same (index := 16) h.valid h.callersValid h.wellFormed (by rw [witness]; exact ofValue_typed (result_typed emptyWitness))
      (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans witness
  let p16 := a23.forgetRefs (emptyCode 16)
  have m16 := m23.prepare (emptyCode 16)
  have tuple16 := prepare_queryTuple tuple23 (emptyCode 16)
  have witness16 : p16.state 16 = Slot.ofValue (encodeResult emptyWitness) :=
    (LoanEnding.forget_closed (emptyCode 16) _ (by rw [witness23]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding)).trans witness23
  have empty2p16 : p16.state 2 = .empty := LoanEnding.forget_empty _ _ empty2a23
  have bound23 : p16.roots 23 = some root23 := by simp [p16, a23, Roots.set, Activation.forgetRefs]
  have bound22p16 : p16.roots 22 = some root22 := by simp [p16, a23, p15, a22, Roots.set, Activation.forgetRefs]
  have uninitialized23 : p16.state 23 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a23, Partial.Locals.set, ite_true]
  have source23 := address_local_source (state := p16.state) (slot := 16) (value := encodeResult emptyWitness)
    (by rw [witness16]; exact Slot.materialize_ofValue _)
  have safeReference : LoanSafe (Slot.ofValue (.reference (encodeResult emptyWitness))) := by
    simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.result emptyWitness)
  obtain ⟨cell23, assign23, ma23⟩ := m16.assign_empty bound23 (w22.allocate_spec _ _).2.1 source23 uninitialized23 m16.safe safeReference (by intros; trivial)
  simp only [Slot.ofValue] at assign23 ma23
  let wa23 := w23.write root23.address cell23
  let aa23 : Activation := {p16 with state := p16.state.set 23 (.shared (encodeResult emptyWitness))}
  change LoanSafeMachine before callers previous external wa23 aa23 at ma23
  have oa23 : LoanOrigin wa23 aa23 before.memory.length 13 :=
    ((o23.prepare (emptyCode 16)).write_other m16.valid bound23 (by decide)
      (by rw [tuple16]; simp [queryTuple, Slot.dropWork, dropFields, DropWork.plus]) (m16.fresh 23 root23 bound23) cell23).congr
      (after := aa23) rfl rfl (by simp only [aa23, p16, Partial.Locals.set, show (13 : Nat) ≠ 23 by decide, ite_false])
  have tupleA23 : aa23.state 13 = queryTuple left right := by simpa only [aa23, Partial.Locals.set, show (13 : Nat) ≠ 23 by decide, ite_false] using tuple16
  have empty2aa23 : aa23.state 2 = .empty := by simpa only [aa23, Partial.Locals.set, show (2 : Nat) ≠ 23 by decide, ite_false] using empty2p16
  have raw22w23 : w23.memory[root22.address]? = some (.node .tuple 0 []) :=
    (w22.allocate_keeps m22.wellFormed _ _ []).memory _ _ (world.allocate_spec _ _).2.1
  have raw22a23 := Activation.write_other_root m16.valid bound23 bound22p16 (by decide) raw22w23 cell23
  let p17 := aa23.forgetRefs (emptyCode 17)
  have m17 := ma23.prepare (emptyCode 17)
  have tuple17 := prepare_queryTuple tupleA23 (emptyCode 17)
  have empty2p17 : p17.state 2 = .empty := LoanEnding.forget_empty _ _ empty2aa23
  have value23 : p17.state 23 = .shared (encodeResult emptyWitness) := by
    rw [Activation.forgetRefs_observed aa23 (emptyCode 17) 23 (by decide +kernel)]
    simp only [aa23, Partial.Locals.set, ite_true]
  have bound22 : p17.roots 22 = some root22 := by change p16.roots 22 = some root22; exact bound22p16
  have uninitialized22 : p17.state 22 = .empty := by
    apply LoanEnding.forget_empty
    simp only [aa23, Partial.Locals.set, show (22 : Nat) ≠ 23 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a23, Partial.Locals.set, show (22 : Nat) ≠ 23 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a22, Partial.Locals.set, ite_true]
  obtain ⟨cell22, assign22, finalMachine⟩ := m17.assign_empty bound22 raw22a23 (address_shared_source value23)
    uninitialized22 m17.safe safeReference (by intros; trivial)
  simp only [Slot.ofValue] at assign22 finalMachine
  let final := wa23.write root22.address cell22
  let after : Activation := {p17 with state := p17.state.set 22 (.shared (encodeResult emptyWitness))}
  change LoanSafeMachine before callers previous external final after at finalMachine
  have finalOrigin : LoanOrigin final after before.memory.length 13 :=
    ((oa23.prepare (emptyCode 17)).write_other m17.valid bound22 (by decide)
      (by rw [tuple17]; simp [queryTuple, Slot.dropWork, dropFields, DropWork.plus]) (m17.fresh 22 root22 bound22) cell22).congr
      (after := after) rfl rfl (by simp only [after, p17, Partial.Locals.set, show (13 : Nat) ≠ 22 by decide, ite_false])
  have tupleAfter : after.state 13 = queryTuple left right := by simpa only [after, Partial.Locals.set, show (13 : Nat) ≠ 22 by decide, ite_false] using tuple17
  have whole : Calling.Prefix callee callers (emptyCode 18) ((emptyActions.drop 14).take 4) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 22) live22)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 23) live23)
        (.cons (Calling.instruction_noncall_run (act := .assign 23 (.address (.local 16))) assign23)
          (.cons (Calling.instruction_noncall_run (act := .assign 22 (.address (.deref (.local 23)))) assign22) (.nil _ _))))
  have empty1After : after.state 1 = .empty :=
    (whole.unshared_local_same (index := 1) h.valid h.callersValid h.wellFormed (by rw [empty1]; intro value same; cases same)
      (by decide +kernel) (by decide +kernel)).trans empty1
  have empty2After : after.state 2 = .empty := by simpa only [after, Partial.Locals.set, show (2 : Nat) ≠ 22 by decide, ite_false] using empty2p17
  have view20After : after.state 20 = .shared (encodeWord left) :=
    (whole.observed_local_same (index := 20) h.valid h.callersValid h.wellFormed
      (by intro offset bound; have small : offset < 4 := by simpa [emptyActions] using bound
          interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans view20
  have view21After : after.state 21 = .shared (encodeWord right) :=
    (whole.observed_local_same (index := 21) h.valid h.callersValid h.wellFormed
      (by intro offset bound; have small : offset < 4 := by simpa [emptyActions] using bound
          interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans view21
  have value22After : after.state 22 = .shared (encodeResult emptyWitness) := by simp only [after, Partial.Locals.set, ite_true]
  have value23After : after.state 23 = .shared (encodeResult emptyWitness) := by simpa only [after, Partial.Locals.set, show (23 : Nat) ≠ 22 by decide, ite_false] using value23
  have wide : ClosedOutside [1, 2, 13, 20, 21, 22, 23] active.state := closed.enlarge (by
    intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  have finalClosed : ClosedOutside [1, 2, 13, 20, 21, 22, 23] after.state :=
    (((((wide.forget (emptyCode 14) _).clear 22).forget (emptyCode 15) _).clear 23).forget (emptyCode 16) _ |>.set_exception (by simp) (.shared (encodeResult emptyWitness))
      |>.forget (emptyCode 17) _).set_exception (by simp) (.shared (encodeResult emptyWitness))
  have data : MemoLoanState after.state := by
    intro index
    by_cases special : index ∈ [1, 2, 13, 20, 21, 22, 23]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at special
      rcases special with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · rw [empty1After]; exact .empty
      · rw [empty2After]; exact .empty
      · rw [tupleAfter]; exact .node (.cons (.shared (.word left)) (.cons (.shared (.word right)) .nil))
      · rw [view20After]; exact .shared (.word left)
      · rw [view21After]; exact .shared (.word right)
      · rw [value22After]; exact .shared (.result emptyWitness)
      · rw [value23After]; exact .shared (.result emptyWitness)
    · obtain ⟨ty, typed, shape⟩ := finalClosed index special
      exact MemoLoans.of_closed typed shape
  refine ⟨final, after, root22, root23, whole, finalMachine, finalOrigin, finalClosed, data, rfl,
    bound22, ?_, ?_, empty1After, empty2After, tupleAfter, view20After, view21After, value22After, value23After, ?_⟩
  · change p16.roots 23 = some root23; exact bound23
  · intro slot twentyTwo twentyThree
    simp only [after, p17, aa23, p16, a23, p15, a22, p14, Activation.forgetRefs, Roots.set, twentyTwo, twentyThree, ite_false]
  · intro slot binding root raw memory
    have twentyTwo : slot ≠ 22 := by intro same; subst slot; rw [unbound22] at root; cases root
    have twentyThree : slot ≠ 23 := by intro same; subst slot; rw [unbound23] at root; cases root
    have rootAt16 : p16.roots slot = some binding := by simpa only [p16, a23, p15, a22, p14, Activation.forgetRefs, Roots.set, twentyTwo, twentyThree, ite_false] using root
    have rootAt17 : p17.roots slot = some binding := by change p16.roots slot = some binding; exact rootAt16
    have w22read : w22.memory[binding.address]? = some raw := (world.allocate_keeps h.wellFormed _ _ []).memory _ _ memory
    have w23read : w23.memory[binding.address]? = some raw := (w22.allocate_keeps m22.wellFormed _ _ []).memory _ _ w22read
    have assignedRead := Activation.write_other_root m16.valid bound23 rootAt16 (Ne.symm twentyThree) w23read cell23
    exact Activation.write_other_root m17.valid bound22 rootAt17 (Ne.symm twentyTwo) assignedRead cell22

end SubtreeProofs.Rust.SourceEval.Evaluator
