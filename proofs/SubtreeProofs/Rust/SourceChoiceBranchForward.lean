module

public import SubtreeProofs.Rust.SourceChoiceForward

/-! Forward construction of either actual choice arm. Both temporary score
roots are retired, then ownership of the selected embedding moves into local
zero. The selected input and its physical representation are arbitrary. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem branch_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : ClosedMachine before callers previous external world active)
    {winner : Nat} (index : winner = 1 ∨ winner = 2) (result : CommonEmbedding)
    (ready : (active.state winner).materialize = some (encodeResult result))
    (empty : active.state 0 = .empty) (four : active.state 4 = .empty) (five : active.state 5 = .empty)
    {returnRoot fourthRoot fifthRoot : Binding}
    (returnBinding : active.roots 0 = some returnRoot) (fourthBinding : active.roots 4 = some fourthRoot)
    (fifthBinding : active.roots 5 = some fifthRoot) :
    ∃ final after,
      ClosedSteps callers world active
        [.storageDead 5, .storageDead 4, .assign 0 (.use (.move (.local winner)))] final after ∧
      ClosedMachine before callers previous external final after ∧
      after.roots = (active.roots.set 5 none).set 4 none ∧ after.count = active.count ∧
      after.state = (active.state.set winner .empty).set 0 (Slot.ofValue (encodeResult result)) := by
  have n0 : winner ≠ 0 := by omega
  have n4 : winner ≠ 4 := by omega
  have n5 : winner ≠ 5 := by omega
  let w5 := world.retire [fifthRoot.address]
  let a5 : Activation := {active with roots := active.roots.set 5 none, state := active.state.set 5 .empty}
  obtain ⟨r5, h5⟩ := h.storageDead fifthBinding (by simp only [five, Slot.dropWork])
  change ClosedMachine before callers previous external w5 a5 at h5
  let w4 := w5.retire [fourthRoot.address]
  let a4 : Activation := {a5 with roots := a5.roots.set 4 none, state := a5.state.set 4 .empty}
  obtain ⟨r4, h4⟩ := h5.storageDead (slot := 4) (binding := fourthRoot)
    (by simpa only [a5, Roots.set, show (4 : Nat) ≠ 5 by decide, ite_false] using fourthBinding)
    (by simp only [a5, Partial.Locals.set, show (4 : Nat) ≠ 5 by decide, ite_false, four, Slot.dropWork])
  change ClosedMachine before callers previous external w4 a4 at h4
  have materialize : (a4.state winner).materialize = some (encodeResult result) := by
    simpa only [a4, a5, Partial.Locals.set, n4, n5, ite_false] using ready
  obtain ⟨cell, run, after⟩ := h4.assign (slot := 0) (binding := returnRoot)
    (by simpa only [a4, a5, Roots.set, show (0 : Nat) ≠ 4 by decide, show (0 : Nat) ≠ 5 by decide,
      ite_false] using returnBinding)
    (rhs := .use (.move (.local winner))) (value := encodeResult result) (middle := a4.state.set winner .empty)
    (by simp only [SourceEval.expression, SourceEval.operand, Partial.Locals.move, splitPlace,
      Slot.take, materialize, bind, Option.bind])
    (by simpa only [a4, a5, Partial.Locals.set, Ne.symm n0, show (0 : Nat) ≠ 4 by decide,
      show (0 : Nat) ≠ 5 by decide, ite_false] using empty)
    trivial (h4.closed.clear winner) (result_typed result) (.adt .embedding)
  refine ⟨_, _, .cons h.closed r5 (.cons h5.closed r4 (.cons h4.closed run (.nil _ _))), after, rfl, rfl, ?_⟩
  funext slot
  by_cases s0 : slot = 0
  · subst slot; simp only [Partial.Locals.set, ite_true]
  · by_cases sw : slot = winner
    · subst slot; simp only [Partial.Locals.set, s0, ite_false, ite_true]
    · by_cases s4 : slot = 4
      · subst slot
        simp only [a4, a5, Partial.Locals.set, s0, sw, ite_false, ite_true, four]
      · by_cases s5 : slot = 5
        · subst slot
          simp only [a4, a5, Partial.Locals.set, s0, sw, s4, ite_false, ite_true, five]
        · simp only [a4, a5, Partial.Locals.set, s0, sw, s4, s5, ite_false]

end SubtreeProofs.Rust.SourceEval.Choice
