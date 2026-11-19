module

public import SubtreeProofs.Rust.SourceEmptyInsertionPrefix
public import SubtreeProofs.Rust.SourceOriginalRetirement

/-! Retire every actual insertion argument/view root and retain the inserted
table, empty witness and return storage for the native result packing suffix. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def emptyArgumentRetired (roots : Roots) : Roots :=
  ((((roots.set 22 none).set 21 none).set 20 none).set 19 none).set 23 none

theorem empty_insert_retire_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : EmptyInsertedScope initial left right table world active) :
    ∃ final after,
      Calling.Prefix callee callers (emptyCode 25) ((emptyActions.drop 19).take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧
      after.roots = emptyArgumentRetired active.roots ∧ after.count = active.count ∧ final.memory = world.memory ∧
      after.state 16 = Slot.ofValue (encodeResult emptyWitness) ∧
      after.state 18 = Slot.ofValue (encodeTable (.Entry ⟨left, right, emptyWitness⟩ table)) ∧
      after.state 0 = .empty ∧ after.state 3 = .empty ∧ after.state 13 = queryTuple left right ∧
      (∃ root0, after.roots 0 = some root0 ∧ final.memory[root0.address]? = some (.node .tuple 0 [])) := by
  obtain ⟨root22, bound22⟩ := scope.live 22 (by simp)
  obtain ⟨root21, bound21⟩ := scope.live 21 (by simp)
  obtain ⟨root20, bound20⟩ := scope.live 20 (by simp)
  obtain ⟨root19, bound19⟩ := scope.live 19 (by simp)
  obtain ⟨root23, bound23⟩ := scope.live 23 (by simp)
  let actions : List Action := [.storageDead 22, .storageDead 21, .storageDead 20, .storageDead 19]
  have plan : RetirementPlan active.roots actions ((((active.roots.set 22 none).set 21 none).set 20 none).set 19 none) := by
    refine .dead bound22 (.dead (binding := root21) ?_ (.dead (binding := root20) ?_ (.dead (binding := root19) ?_ (.nil _))))
    all_goals simp only [Roots.set, show (21 : Nat) ≠ 22 by decide, show (20 : Nat) ≠ 22 by decide,
      show (20 : Nat) ≠ 21 by decide, show (19 : Nat) ≠ 22 by decide, show (19 : Nat) ≠ 21 by decide,
      show (19 : Nat) ≠ 20 by decide, ite_false]
    all_goals assumption
  have zero : ZeroRetirement actions active.state := by
    intro slot member
    simp [actions] at member
    rcases member with rfl | rfl | rfl | rfl <;> rw [scope.empty _ (by simp)] <;> simp only [Slot.dropWork]
  obtain ⟨middle, current, first, machine, roots, count, memory⟩ := plan.complete_original callee (emptyCode 23) h rfl zero
  let p23 := current.forgetRefs (emptyCode 23)
  have m23 := machine.prepare (emptyCode 23)
  let p24 := p23.forgetRefs (emptyCode 24)
  have m24 := m23.prepare (emptyCode 24)
  have bound23p24 : p24.roots 23 = some root23 := by
    simpa [p24, p23, Activation.forgetRefs, roots, Roots.set] using bound23
  have empty23 : p24.state 23 = .empty := by
    apply LoanEnding.forget_empty
    apply LoanEnding.forget_empty
    exact (first.closed_local_same (index := 23) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.empty 23 (by simp)]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans (scope.empty 23 (by simp))
  obtain ⟨end23, finalMachine⟩ := m24.storageDead bound23p24 (by rw [empty23]; simp only [Slot.dropWork])
  let final := middle.retire [root23.address]
  let after : Activation := {p24 with roots := p24.roots.set 23 none, state := p24.state.set 23 .empty}
  change OriginalLoanMachine before callers previous external [1, 2, 13] final after at finalMachine
  have tail : Calling.Prefix callee callers (emptyCode 25) [.fakeRead (.local 18), .storageDead 23] middle current final after :=
    .cons (Calling.instruction_noncall_run (act := .fakeRead (.local 18)) rfl)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 23) end23) (.nil _ _))
  have whole : Calling.Prefix callee callers (emptyCode 25) ((emptyActions.drop 19).take 6) world active final after :=
    Calling.Prefix.append (suffix := emptyCode 25) (rest := [.fakeRead (.local 18), .storageDead 23]) first tail
  have rootsAfter : after.roots = emptyArgumentRetired active.roots := by
    change p24.roots.set 23 none = _
    change current.roots.set 23 none = _
    rw [roots]
    rfl
  refine ⟨final, after, whole, finalMachine, rootsAfter, count, memory, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (whole.closed_local_same (index := 16) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.witness]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.witness
  · exact (whole.closed_local_same (index := 18) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.table]; exact ofValue_typed (table_typed _)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.table
  · exact (whole.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.empty 0 (by simp)]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans (scope.empty 0 (by simp))
  · exact (whole.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.empty 3 (by simp)]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans (scope.empty 3 (by simp))
  · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  · obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
    refine ⟨root0, ?_, ?_⟩
    · simpa [rootsAfter, emptyArgumentRetired, Roots.set] using bound0
    · rw [show final.memory = world.memory from memory]; exact raw0

end SubtreeProofs.Rust.SourceEval.Evaluator
