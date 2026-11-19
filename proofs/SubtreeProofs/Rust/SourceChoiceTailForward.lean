module

public import SubtreeProofs.Rust.SourceChoiceBranchForward

/-! Construct choice's losing-value drops, remaining storage retirement and
actual return. The two input locals may contain arbitrarily large owned words;
complete ownership and represented caller-loan permissions justify destruction. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def tail : Code :=
  .step (.storageDead 3) <| .step (.drop 2) <| .step (.drop 1) <|
  .step (.storageDead 2) <| .step (.storageDead 1) .ret

theorem tail_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : ClosedMachine before callers previous external world active) (callee : Derived.Callees)
    {value : Value} (ready : (active.state 0).materialize = some value)
    (three : active.state 3 = .empty)
    (others : ∀ slot, slot ≠ 0 → slot ≠ 1 → slot ≠ 2 → slot ≠ 3 → active.state slot = .empty)
    {returnRoot firstRoot secondRoot thirdRoot : Binding}
    (returnBinding : active.roots 0 = some returnRoot) (firstBinding : active.roots 1 = some firstRoot)
    (secondBinding : active.roots 2 = some secondRoot) (thirdBinding : active.roots 3 = some thirdRoot) :
    ∃ final after cell cost,
      Calling.exec callee callers tail world active = some (.returned final after (cell, value), cost) ∧
      (∀ slot, after.state slot = .empty) ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      after.RootsSeparate callers := by
  let w3 := world.retire [thirdRoot.address]
  let a3 : Activation := {active with roots := active.roots.set 3 none, state := active.state.set 3 .empty}
  obtain ⟨r3, h3⟩ := h.storageDead thirdBinding (by simp only [three, Slot.dropWork])
  change ClosedMachine before callers previous external w3 a3 at h3
  obtain ⟨d2, r2, h2, _⟩ := h3.drop (slot := 2) (binding := secondRoot)
    (by simpa only [a3, Roots.set, show (2 : Nat) ≠ 3 by decide, ite_false] using secondBinding)
  let w2 := w3.retire d2
  let a2 : Activation := {a3 with state := a3.state.set 2 .empty}
  change ClosedMachine before callers previous external w2 a2 at h2
  obtain ⟨d1, r1, h1, _⟩ := h2.drop (slot := 1) (binding := firstRoot)
    (by simpa only [a2, a3, Roots.set, show (1 : Nat) ≠ 3 by decide, ite_false] using firstBinding)
  let w1 := w2.retire d1
  let a1 : Activation := {a2 with state := a2.state.set 1 .empty}
  change ClosedMachine before callers previous external w1 a1 at h1
  let ws2 := w1.retire [secondRoot.address]
  let as2 : Activation := {a1 with roots := a1.roots.set 2 none, state := a1.state.set 2 .empty}
  obtain ⟨rs2, hs2⟩ := h1.storageDead (slot := 2) (binding := secondRoot)
    (by simpa only [a1, a2, a3, Roots.set, show (2 : Nat) ≠ 3 by decide, ite_false] using secondBinding)
    (by simp only [a1, a2, Partial.Locals.set, show (2 : Nat) ≠ 1 by decide, ite_false, ite_true, Slot.dropWork])
  change ClosedMachine before callers previous external ws2 as2 at hs2
  let ws1 := ws2.retire [firstRoot.address]
  let as1 : Activation := {as2 with roots := as2.roots.set 1 none, state := as2.state.set 1 .empty}
  obtain ⟨rs1, hs1⟩ := hs2.storageDead (slot := 1) (binding := firstRoot)
    (by simpa only [as2, a1, a2, a3, Roots.set, show (1 : Nat) ≠ 2 by decide,
      show (1 : Nat) ≠ 3 by decide, ite_false] using firstBinding)
    (by simp only [as2, a1, Partial.Locals.set, show (1 : Nat) ≠ 2 by decide, ite_false, ite_true, Slot.dropWork])
  change ClosedMachine before callers previous external ws1 as1 at hs1
  have hb : as1.roots 0 = some returnRoot := by
    simpa only [as1, as2, a1, a2, a3, Roots.set, show (0 : Nat) ≠ 1 by decide,
      show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 3 by decide, ite_false] using returnBinding
  have materialize : (as1.state 0).materialize = some value := by
    simpa only [as1, as2, a1, a2, a3, Partial.Locals.set, show (0 : Nat) ≠ 1 by decide,
      show (0 : Nat) ≠ 2 by decide, show (0 : Nat) ≠ 3 by decide, ite_false] using ready
  obtain ⟨cell, returned⟩ := Derived.returnValue_complete hs1.valid hs1.callersValid hs1.separate hs1.ownerFrame hb materialize
    (Derived.ReturnLoansAllowed.of_closed_preserved (fun index _ => hs1.closed index)
      hs1.previousCallers hs1.beforeWellFormed hs1.kept (hs1.fresh 0 returnRoot hb))
  have steps : ClosedSteps callers world active [.storageDead 3, .drop 2, .drop 1, .storageDead 2, .storageDead 1] ws1 as1 :=
    .cons h.closed r3 (.cons h3.closed r2 (.cons h2.closed r1 (.cons h1.closed rs2 (.cons hs2.closed rs1 (.nil _ _)))))
  obtain ⟨cost, run⟩ := steps.exec callee (rest := .ret) returned
  refine ⟨_, _, cell, cost, run, ?_, hs1.fresh, hs1.separate⟩
  intro slot
  by_cases s0 : slot = 0
  · subst slot; simp only [Partial.Locals.set, ite_true]
  · by_cases s1 : slot = 1
    · subst slot; simp only [as1, Partial.Locals.set, s0, ite_false, ite_true]
    · by_cases s2 : slot = 2
      · subst slot; simp only [as1, as2, Partial.Locals.set, s0, s1, ite_false, ite_true]
      · by_cases s3 : slot = 3
        · subst slot; simp only [as1, as2, a1, a2, a3, Partial.Locals.set, s0, s1, s2, ite_false, ite_true]
        · simpa only [as1, as2, a1, a2, a3, Partial.Locals.set, s0, s1, s2, s3, ite_false] using others slot s0 s1 s2 s3

end SubtreeProofs.Rust.SourceEval.Choice
