module

public import SubtreeProofs.Rust.SourcePrefixLocals

/-! Execute finite drop/retirement plans whose selected locals contain no box
owners. The existing executor retains its actual destructor visits, reference
preparation, root guards and storage retirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

inductive RetirementPlan : Roots → List Action → Roots → Prop where
  | nil (roots) : RetirementPlan roots [] roots
  | drop {roots final : Roots} {slot : Nat} {binding : Binding} {rest : List Action}
      (bound : roots slot = some binding) (tail : RetirementPlan roots rest final) :
      RetirementPlan roots (.drop slot :: rest) final
  | dead {roots final : Roots} {slot : Nat} {binding : Binding} {rest : List Action}
      (bound : roots slot = some binding) (tail : RetirementPlan (roots.set slot none) rest final) :
      RetirementPlan roots (.storageDead slot :: rest) final

def ZeroRetirement (actions : List Action) (state : State) : Prop :=
  ∀ slot, Action.drop slot ∈ actions ∨ Action.storageDead slot ∈ actions → (state slot).dropWork.boxes = 0

theorem prepare_zero_work (code : Code) (active : Activation) {slot : Nat}
    (zero : (active.state slot).dropWork.boxes = 0) : ((active.forgetRefs code).state slot).dropWork.boxes = 0 := by
  change (LoanEnding.forget code (List.range active.count) active.state slot).dropWork.boxes = 0
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
  · rw [same]; exact zero
  · rw [empty]; simp only [Slot.dropWork]

theorem ZeroRetirement.tail_clear {act : Action} {rest : List Action} {active : Activation}
    (zero : ZeroRetirement (act :: rest) active.state) (code : Code) (index : Nat) :
    ZeroRetirement rest ((active.forgetRefs code).state.set index .empty) := by
  intro slot member
  by_cases same : slot = index
  · subst slot; simp only [Partial.Locals.set, ite_true, Slot.dropWork]
  · simp only [Partial.Locals.set, same, ite_false]
    exact prepare_zero_work code active (zero slot (member.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _)))

theorem RetirementPlan.complete {before : World} {callers : List Activation} {previous : Resources}
    {external : List Nat} (callee : Derived.Callees) (suffix : Code)
    {roots finalRoots : Roots} {actions : List Action} (plan : RetirementPlan roots actions finalRoots) :
    ∀ {world : World} {active : Activation}, QueryMachine before callers previous external world active →
      active.roots = roots → ZeroRetirement actions active.state →
      ∃ final after, Calling.Prefix callee callers suffix actions world active final after ∧
        QueryMachine before callers previous external final after ∧ after.roots = finalRoots ∧ after.count = active.count := by
  induction plan with
  | nil roots =>
    intro world active machine rootsEq zero
    exact ⟨world, active, .nil _ _, machine, rootsEq, rfl⟩
  | @drop roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq zero
    let code := (Action.drop slot :: rest).foldr Control.Tree.step suffix
    have prepared := machine.prepare code
    have hb : (active.forgetRefs code).roots slot = some binding := by rw [show (active.forgetRefs code).roots = active.roots from rfl, rootsEq]; exact bound
    obtain ⟨run, next⟩ := prepared.drop_zero hb (prepare_zero_work code active (zero slot (Or.inl (by simp))))
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter⟩ := ih next rootsEq (zero.tail_clear code slot)
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .drop slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter⟩
  | @dead roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq zero
    let code := (Action.storageDead slot :: rest).foldr Control.Tree.step suffix
    have prepared := machine.prepare code
    have hb : (active.forgetRefs code).roots slot = some binding := by rw [show (active.forgetRefs code).roots = active.roots from rfl, rootsEq]; exact bound
    obtain ⟨run, next⟩ := prepared.storageDead hb (prepare_zero_work code active (zero slot (Or.inr (by simp))))
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter⟩ := ih next (by change active.roots.set slot none = roots.set slot none; rw [rootsEq]) (zero.tail_clear code slot)
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .storageDead slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter⟩

end SubtreeProofs.Rust.SourceEval.Addressed
