module

public import SubtreeProofs.Rust.SourceEvaluatorLookupPrefix
public import SubtreeProofs.Rust.SourceCallRootPreservation
public import SubtreeProofs.Rust.SourceNativeStorageRetirement
import Mathlib.Tactic.IntervalCases

/-! Construct the three actual storage-dead instructions following lookup,
with the pinned switch as their real continuation. Pointer bits are retained by
the call even after argument moves clear their logical masks. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def lookupSwitch : Code :=
  .switch (.discriminant (.local 4)) [(.variant .optional 1, 0)] (some 1) cacheHit cacheMiss returnResult

def lookupRetire : List Action := [.storageDead 8, .storageDead 7, .storageDead 5]

def retireCode (index : Nat) : Code := (lookupRetire.drop index).foldr Control.Tree.step lookupSwitch

theorem afterLookup_retire : afterLookup = lookupRetire.foldr Control.Tree.step lookupSwitch := rfl

theorem retire_observes (index : Nat) (bound : index ≤ 3) (slot : Nat) (member : slot ∈ [1, 2, 3, 4]) :
    LoanEnding.endsBeforeObservation slot (retireCode index) = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl <;> interval_cases index <;> decide +kernel

theorem InputLocals.prepare_retire {left right : BalancedWord} {table : MemoTable} {active : Activation}
    (h : InputLocals left right table active.state) (index : Nat) (bound : index ≤ 3) :
    InputLocals left right table (active.forgetRefs (retireCode index)).state := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Activation.forgetRefs_observed active _ 1 (retire_observes index bound 1 (by simp))]; exact h.left
  · rw [Activation.forgetRefs_observed active _ 2 (retire_observes index bound 2 (by simp))]; exact h.right
  · rw [Activation.forgetRefs_observed active _ 3 (retire_observes index bound 3 (by simp))]; exact h.table

theorem retire_lookup_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    (left right : BalancedWord) (table : MemoTable) (inputs : InputLocals left right table active.state)
    {tableView leftView rightView : Binding} {tablePointer leftPointer rightPointer : Pointer}
    (tableBinding : active.roots 5 = some tableView) (leftBinding : active.roots 7 = some leftView)
    (rightBinding : active.roots 8 = some rightView)
    (tableMemory : world.memory[tableView.address]? = some (.shared tablePointer))
    (leftMemory : world.memory[leftView.address]? = some (.shared leftPointer))
    (rightMemory : world.memory[rightView.address]? = some (.shared rightPointer))
    (tableEmpty : active.state 5 = .empty) (leftEmpty : active.state 7 = .empty) (rightEmpty : active.state 8 = .empty) :
    ∃ final after,
      Calling.Prefix callee callers lookupSwitch lookupRetire world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.roots = ((active.roots.set 8 none).set 7 none).set 5 none ∧ after.count = active.count ∧
      after.state 4 = active.state 4 ∧ final.memory = world.memory ∧
      (∀ index, index ∉ [5, 7, 8] → active.state index = .empty → after.state index = .empty) := by
  let p8 := active.forgetRefs (retireCode 0)
  have h8 := h.prepare (retireCode 0)
  have i8 := inputs.prepare_retire 0 (by decide)
  let w8 := world.retire [rightView.address]
  let a8 : Activation := {p8 with roots := p8.roots.set 8 none, state := p8.state.set 8 .empty}
  obtain ⟨r8, m8⟩ := h8.storageDead_reference rightBinding rightMemory
    (by rw [show p8.state 8 = .empty from LoanEnding.forget_empty _ _ rightEmpty]; simp only [Slot.dropWork])
  change LoanSafeMachine before callers previous external w8 a8 at m8
  have ia8 : InputLocals left right table a8.state := i8.set 8 .empty (by simp)
  let p7 := a8.forgetRefs (retireCode 1)
  have h7 := m8.prepare (retireCode 1)
  have i7 := ia8.prepare_retire 1 (by decide)
  let w7 := w8.retire [leftView.address]
  let a7 : Activation := {p7 with roots := p7.roots.set 7 none, state := p7.state.set 7 .empty}
  have leftStill : p7.roots 7 = some leftView := by simpa [p7, a8, p8, Activation.forgetRefs, Roots.set] using leftBinding
  have empty7 : p7.state 7 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a8, Partial.Locals.set, show (7 : Nat) ≠ 8 by decide, ite_false]
    exact LoanEnding.forget_empty (retireCode 0) _ leftEmpty
  obtain ⟨r7, m7⟩ := h7.storageDead_reference leftStill leftMemory (by rw [empty7]; simp only [Slot.dropWork])
  change LoanSafeMachine before callers previous external w7 a7 at m7
  have ia7 : InputLocals left right table a7.state := i7.set 7 .empty (by simp)
  let p5 := a7.forgetRefs (retireCode 2)
  have h5 := m7.prepare (retireCode 2)
  have i5 := ia7.prepare_retire 2 (by decide)
  let final := w7.retire [tableView.address]
  let after : Activation := {p5 with roots := p5.roots.set 5 none, state := p5.state.set 5 .empty}
  have tableStill : p5.roots 5 = some tableView := by
    simpa [p5, a7, p7, a8, p8, Activation.forgetRefs, Roots.set] using tableBinding
  have empty5 : p5.state 5 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a7, Partial.Locals.set, show (5 : Nat) ≠ 7 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a8, Partial.Locals.set, show (5 : Nat) ≠ 8 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ tableEmpty
  obtain ⟨r5, m5⟩ := h5.storageDead_reference tableStill tableMemory (by rw [empty5]; simp only [Slot.dropWork])
  change LoanSafeMachine before callers previous external final after at m5
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .storageDead 8) r8)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 7) r7)
        (.cons (Calling.instruction_noncall_run (act := .storageDead 5) r5) (.nil _ _))),
    m5, i5.set 5 .empty (by simp), rfl, rfl, ?_, rfl, ?_⟩
  · simp only [after, Partial.Locals.set, show (4 : Nat) ≠ 5 by decide, ite_false]
    rw [Activation.forgetRefs_observed a7 _ 4 (retire_observes 2 (by decide) 4 (by simp))]
    simp only [a7, Partial.Locals.set, show (4 : Nat) ≠ 7 by decide, ite_false]
    rw [Activation.forgetRefs_observed a8 _ 4 (retire_observes 1 (by decide) 4 (by simp))]
    simp only [a8, Partial.Locals.set, show (4 : Nat) ≠ 8 by decide, ite_false]
    rw [Activation.forgetRefs_observed active _ 4 (retire_observes 0 (by decide) 4 (by simp))]
  · intro index member empty
    have five : index ≠ 5 := by intro same; subst index; simp at member
    have seven : index ≠ 7 := by intro same; subst index; simp at member
    have eight : index ≠ 8 := by intro same; subst index; simp at member
    simp only [after, Partial.Locals.set, five, ite_false]
    apply LoanEnding.forget_empty
    simp only [a7, Partial.Locals.set, seven, ite_false]
    apply LoanEnding.forget_empty
    simp only [a8, Partial.Locals.set, eight, ite_false]
    exact LoanEnding.forget_empty _ _ empty

end SubtreeProofs.Rust.SourceEval.Evaluator
