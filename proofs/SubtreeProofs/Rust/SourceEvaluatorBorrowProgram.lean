module

public import SubtreeProofs.Rust.SourceQueryLoanOrigins
public import SubtreeProofs.Rust.SourceEvalBodyCertificate
import Mathlib.Tactic.IntervalCases

/-! The actual evaluator's common borrow prefix, with its actual continuation
retained for reference-view preparation. The split is definitionally the pinned
body, not a replacement control interpreter. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def borrowPrefix : List Action :=
  [.storageLive 0, .storageLive 4, .storageLive 5, .storageLive 6,
   .assign 6 (.address (.local 3)), .assign 5 (.address (.deref (.local 6))),
   .storageLive 7, .assign 7 (.address (.deref (.local 1))),
   .storageLive 8, .assign 8 (.address (.deref (.local 2)))]

def lookupSuffix : Code :=
  .step (.call .lookup [.move (.local 5), .move (.local 7), .move (.local 8)] 4) <|
  .step (.storageDead 8) <| .step (.storageDead 7) <| .step (.storageDead 5) <|
  .switch (.discriminant (.local 4)) [(.variant .optional 1, 0)] (some 1) cacheHit cacheMiss returnResult

def borrowCode (index : Nat) : Code := (borrowPrefix.drop index).foldr Control.Tree.step lookupSuffix

theorem body_borrow_prefix : body = borrowPrefix.foldr Control.Tree.step lookupSuffix := rfl

theorem borrow_observes_inputs (index : Nat) (bound : index ≤ 10) (slot : Nat) (member : slot ∈ [1, 2, 3]) :
    LoanEnding.endsBeforeObservation slot (borrowCode index) = false := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl <;> interval_cases index <;> decide +kernel

structure InputLocals (left right : BalancedWord) (table : MemoTable) (state : State) : Prop where
  left : state 1 = .shared (encodeWord left)
  right : state 2 = .shared (encodeWord right)
  table : state 3 = Slot.ofValue (encodeTable table)

theorem InputLocals.references {left right : BalancedWord} {table : MemoTable} {state : State}
    (h : InputLocals left right table state) : ReferenceQueries state := by
  intro slot member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl
  · exact Or.inr ⟨encodeWord left, h.left⟩
  · exact Or.inr ⟨encodeWord right, h.right⟩

theorem InputLocals.prepare {left right : BalancedWord} {table : MemoTable} {active : Activation}
    (h : InputLocals left right table active.state) (index : Nat) (bound : index ≤ 10) :
    InputLocals left right table (active.forgetRefs (borrowCode index)).state := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Activation.forgetRefs_observed active _ 1 (borrow_observes_inputs index bound 1 (by simp))]; exact h.left
  · rw [Activation.forgetRefs_observed active _ 2 (borrow_observes_inputs index bound 2 (by simp))]; exact h.right
  · rw [Activation.forgetRefs_observed active _ 3 (borrow_observes_inputs index bound 3 (by simp))]; exact h.table

theorem InputLocals.set {left right : BalancedWord} {table : MemoTable} {state : State}
    (h : InputLocals left right table state) (slot : Nat) (part : Slot) (other : slot ∉ [1, 2, 3]) :
    InputLocals left right table (state.set slot part) := by
  have one : (1 : Nat) ≠ slot := by intro same; subst slot; simp at other
  have two : (2 : Nat) ≠ slot := by intro same; subst slot; simp at other
  have three : (3 : Nat) ≠ slot := by intro same; subst slot; simp at other
  exact ⟨by simpa only [Partial.Locals.set, one, ite_false] using h.left,
    by simpa only [Partial.Locals.set, two, ite_false] using h.right,
    by simpa only [Partial.Locals.set, three, ite_false] using h.table⟩

theorem address_local_source {state : State} {slot : Nat} {value : Value}
    (materialize : (state slot).materialize = some value) :
    SourceEval.expression state (.address (.local slot)) = some (.reference value, state) := by
  simp only [SourceEval.expression, Partial.Locals.read, splitPlace, Slot.read, Slot.get, materialize, bind, Option.bind]

theorem address_shared_source {state : State} {slot : Nat} {value : Value} (initialized : state slot = .shared value) :
    SourceEval.expression state (.address (.deref (.local slot))) = some (.reference value, state) := by
  simp only [SourceEval.expression, Partial.Locals.read, splitPlace, List.nil_append, initialized, Slot.read, Slot.get,
    Slot.materialize_ofValue, bind, Option.bind]

theorem Activation.write_other_root {world : World} {active : Activation} (h : active.Valid world)
    {slot other : Nat} {binding target : Binding} (hb : active.roots slot = some binding)
    (ht : active.roots other = some target) (different : slot ≠ other) {raw : Cell}
    (memory : world.memory[target.address]? = some raw) (cell : Cell) :
    (world.write binding.address cell).memory[target.address]? = some raw := by
  obtain ⟨_, frame⟩ := h.2
  have distinct : binding.address ≠ target.address := fun eq => different (frame.distinct hb ht eq)
  simpa only [World.write, List.getElem?_set_ne distinct] using memory

end SubtreeProofs.Rust.SourceEval.Evaluator
