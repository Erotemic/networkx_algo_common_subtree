module

public import SubtreeProofs.Rust.SourceChoiceTailForward

/-! Whole-body physical success for the pinned choice control. Independent
native inputs, closed valid storage, fresh roots and legal ownership transfer
construct the selected actual execution, including ties and losing-value drops.
Entry and guarded output cleanup are separate boundaries. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem initial_empty (first second : CommonEmbedding) {slot : Nat} (one : slot ≠ 1) (two : slot ≠ 2) :
    initialState [encodeResult first, encodeResult second] slot = .empty := by
  by_cases zero : slot = 0
  · subst slot; rfl
  · have bound : 2 ≤ slot - 1 := by omega
    have out : [encodeResult first, encodeResult second][slot - 1]? = none :=
      List.getElem?_eq_none (by simpa only [List.length_cons, List.length_nil] using bound)
    simp only [initialState, Partial.Locals.lift, initialEnv, zero, ite_false, out]

theorem selected_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : ClosedMachine before callers previous external world active) (callee : Derived.Callees)
    (first second : CommonEmbedding) (state : active.state = initialState [encodeResult first, encodeResult second])
    {winner : Nat} (index : winner = 1 ∨ winner = 2) (result : CommonEmbedding)
    (ready : (active.state winner).materialize = some (encodeResult result))
    {returnRoot firstRoot secondRoot thirdRoot fourthRoot fifthRoot : Binding}
    (returnBinding : active.roots 0 = some returnRoot) (firstBinding : active.roots 1 = some firstRoot)
    (secondBinding : active.roots 2 = some secondRoot) (thirdBinding : active.roots 3 = some thirdRoot)
    (fourthBinding : active.roots 4 = some fourthRoot) (fifthBinding : active.roots 5 = some fifthRoot) :
    ∃ middle current firstCost final after cell lastCost,
      Calling.exec callee callers (branch winner) world active = some (.next middle current, firstCost) ∧
      Calling.exec callee callers tail middle current = some (.returned final after (cell, encodeResult result), lastCost) ∧
      (∀ slot, after.state slot = .empty) ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      after.RootsSeparate callers := by
  obtain ⟨middle, current, steps, machine, roots, _, masks⟩ := branch_complete h index result ready
    (by simpa only [state] using initial_empty first second (slot := 0) (by decide) (by decide))
    (by simpa only [state] using initial_empty first second (slot := 4) (by decide) (by decide))
    (by simpa only [state] using initial_empty first second (slot := 5) (by decide) (by decide))
    returnBinding fourthBinding fifthBinding
  obtain ⟨firstCost, branchRun⟩ := steps.exec callee (rest := .done) (Calling.exec_done callee callers middle current)
  obtain ⟨final, after, cell, lastCost, tailRun, empty, fresh, separate⟩ := tail_complete machine callee
    (value := encodeResult result)
    (by rw [masks]; simp only [Partial.Locals.set, ite_true, Slot.materialize_ofValue])
    (by rw [masks]; simp only [Partial.Locals.set, show (3 : Nat) ≠ 0 by decide,
      show (3 : Nat) ≠ winner by omega, ite_false, state]; exact initial_empty first second (by decide) (by decide))
    (by
      intro slot s0 s1 s2 _
      rw [masks]
      simp only [Partial.Locals.set, s0, show slot ≠ winner by omega, ite_false, state]
      exact initial_empty first second s1 s2)
    (returnRoot := returnRoot) (firstRoot := firstRoot) (secondRoot := secondRoot) (thirdRoot := thirdRoot)
    (by simpa only [roots, Roots.set, show (0 : Nat) ≠ 4 by decide, show (0 : Nat) ≠ 5 by decide, ite_false] using returnBinding)
    (by simpa only [roots, Roots.set, show (1 : Nat) ≠ 4 by decide, show (1 : Nat) ≠ 5 by decide, ite_false] using firstBinding)
    (by simpa only [roots, Roots.set, show (2 : Nat) ≠ 4 by decide, show (2 : Nat) ≠ 5 by decide, ite_false] using secondBinding)
    (by simpa only [roots, Roots.set, show (3 : Nat) ≠ 4 by decide, show (3 : Nat) ≠ 5 by decide, ite_false] using thirdBinding)
  exact ⟨middle, current, firstCost, final, after, cell, lastCost, branchRun, tailRun, empty, fresh, separate⟩

theorem body_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : ClosedMachine before callers previous external world active) (callee : Derived.Callees)
    (count : active.count = 6) (first second : CommonEmbedding)
    (state : active.state = initialState [encodeResult first, encodeResult second])
    (zero : active.roots 0 = none) (three : active.roots 3 = none)
    (four : active.roots 4 = none) (five : active.roots 5 = none)
    {firstRoot secondRoot : Binding} (firstBinding : active.roots 1 = some firstRoot)
    (secondBinding : active.roots 2 = some secondRoot) :
    ∃ final after cell cost,
      Calling.exec callee callers body world active =
        some (.returned final after (cell, encodeResult (OrderedSolver.selectResult first second)), cost) ∧
      (∀ slot, after.state slot = .empty) ∧
      (∀ slot binding, after.roots slot = some binding → before.memory.length ≤ binding.address) ∧
      after.RootsSeparate callers := by
  obtain ⟨preparedWorld, prepared, steps, machine, _, masks, firstKept, secondKept,
    ⟨returnRoot, returnBinding⟩, ⟨thirdRoot, thirdBinding⟩, ⟨fourthRoot, fourthBinding⟩, ⟨fifthRoot, fifthBinding⟩⟩ :=
    prelude_complete h count first second state zero three four five
  obtain ⟨inspect, inspected⟩ := machine.switchBool (slot := 3)
    (value := decide (first.edges.val < second.edges.val)) (by rw [masks]; simp only [Partial.Locals.set, ite_true])
  let queried : Activation := {prepared with state := prepared.state.set 3 .empty}
  change ClosedMachine before callers previous external preparedWorld queried at inspected
  have queryState : queried.state = initialState [encodeResult first, encodeResult second] := by
    funext slot
    by_cases same : slot = 3
    · subst slot
      simp only [queried, Partial.Locals.set, ite_true]
      exact (initial_empty first second (by decide) (by decide)).symm
    · simp only [queried, masks, Partial.Locals.set, same, ite_false]
  let winner : Nat := if first.edges.val < second.edges.val then 2 else 1
  have index : winner = 1 ∨ winner = 2 := by unfold winner; split <;> simp
  have ready : (queried.state winner).materialize = some (encodeResult (OrderedSolver.selectResult first second)) := by
    rw [queryState]
    by_cases cmp : first.edges.val < second.edges.val <;>
      simp [winner, cmp, OrderedSolver.selectResult, initialState, Partial.Locals.lift, initialEnv, Slot.materialize_ofValue]
  obtain ⟨middle, current, firstCost, final, after, cell, lastCost, branchRun, tailRun, empty, fresh, separate⟩ :=
    selected_complete inspected callee first second queryState index (OrderedSolver.selectResult first second) ready
      returnBinding (firstKept.trans firstBinding) (secondKept.trans secondBinding) thirdBinding fourthBinding fifthBinding
  have selected : Control.selectSource (.boolean (decide (first.edges.val < second.edges.val)))
      [(.boolean false, 1)] (some 0)
      (fun _ => Calling.exec callee callers (branch 2) preparedWorld queried)
      (fun _ => Calling.exec callee callers (branch 1) preparedWorld queried) = some (.next middle current, firstCost) := by
    by_cases cmp : first.edges.val < second.edges.val <;>
      simpa [winner, cmp,
        Control.selectSource, Control.selectIndex, reduceCtorEq, Bool.false_eq_true, ite_false, ite_true,
        bind, Option.bind] using branchRun
  have switchRun : Calling.exec callee callers
      (.switch (.value (.move 3)) [(.boolean false, 1)] (some 0) (branch 2) (branch 1) tail)
      preparedWorld prepared = some (.returned final after (cell, encodeResult (OrderedSolver.selectResult first second)),
        ((Cost.local (1 + (Scrutinee.value (.move 3)).weight)).plus firstCost).plus lastCost) := by
    rw [Calling.exec_switch, inspect]
    change (do
      let (result, work) : Derived.Flow × Cost ← Control.selectSource _ _ _
        (fun _ => Calling.exec callee callers (branch 2) preparedWorld queried)
        (fun _ => Calling.exec callee callers (branch 1) preparedWorld queried)
      match result with
      | .returned final after packet => some (Derived.Flow.returned final after packet, (Cost.local _).plus work)
      | .next middle current => do
        let (flow, last) ← Calling.exec callee callers tail middle current
        some (flow, ((Cost.local _).plus work).plus last)) = _
    simp only [selected, tailRun, bind, Option.bind]
  obtain ⟨cost, run⟩ := steps.exec callee switchRun
  exact ⟨final, after, cell, cost, run, empty, fresh, separate⟩

end SubtreeProofs.Rust.SourceEval.Choice
