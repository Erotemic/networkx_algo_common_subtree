module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine
public import SubtreeProofs.Rust.SourceQueryRetirement

/-! Execute existing finite retirement plans with an arbitrary original-loan
family. Exact memory preservation records symbolic storage retirement, while
the existing executor retains all destructor visits and root/loan checks. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem RetirementPlan.complete_original {before : World} {callers : List Activation} {previous : Resources}
    {external exceptions : List Nat} (callee : Derived.Callees) (suffix : Code)
    {roots finalRoots : Roots} {actions : List Action} (plan : RetirementPlan roots actions finalRoots) :
    ∀ {world : World} {active : Activation}, OriginalLoanMachine before callers previous external exceptions world active →
      active.roots = roots → ZeroRetirement actions active.state →
      ∃ final after, Calling.Prefix callee callers suffix actions world active final after ∧
        OriginalLoanMachine before callers previous external exceptions final after ∧ after.roots = finalRoots ∧
        after.count = active.count ∧ final.memory = world.memory := by
  induction plan with
  | nil roots =>
    intro world active machine rootsEq zero
    exact ⟨world, active, .nil _ _, machine, rootsEq, rfl, rfl⟩
  | @drop roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq zero
    let code := (Action.drop slot :: rest).foldr Control.Tree.step suffix
    have prepared := machine.prepare code
    have hb : (active.forgetRefs code).roots slot = some binding := by
      change active.roots slot = some binding; rw [rootsEq]; exact bound
    obtain ⟨run, next⟩ := prepared.drop_zero hb (prepare_zero_work code active (zero slot (Or.inl (by simp))))
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter, memoryAfter⟩ := ih next rootsEq (zero.tail_clear code slot)
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .drop slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter, memoryAfter⟩
  | @dead roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq zero
    let code := (Action.storageDead slot :: rest).foldr Control.Tree.step suffix
    have prepared := machine.prepare code
    have hb : (active.forgetRefs code).roots slot = some binding := by
      change active.roots slot = some binding; rw [rootsEq]; exact bound
    obtain ⟨run, next⟩ := prepared.storageDead hb (prepare_zero_work code active (zero slot (Or.inr (by simp))))
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter, memoryAfter⟩ :=
      ih next (by change active.roots.set slot none = roots.set slot none; rw [rootsEq]) (zero.tail_clear code slot)
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .storageDead slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Addressed
