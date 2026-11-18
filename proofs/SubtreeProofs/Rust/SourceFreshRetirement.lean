module

public import SubtreeProofs.Rust.SourceRetirementPresence
public import SubtreeProofs.Rust.SourceOriginalOwnedDrop
public import SubtreeProofs.Rust.SourcePrefixOwnerProvenance

/-! Mixed cleanup constructs fresh owned drops and zero-owner storage endings.
The count check clears a local after its drop; it therefore permits nonempty
owned query temporaries without asking that their initial masks be empty. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def clearBoxCount (boxes : Nat → Nat) (slot : Nat) : Nat → Nat :=
  fun index => if index = slot then 0 else boxes index

def retirementZeroChecks (boxes : Nat → Nat) : List Action → Prop
  | [] => True
  | .drop slot :: rest => retirementZeroChecks (clearBoxCount boxes slot) rest
  | .storageDead slot :: rest => boxes slot = 0 ∧ retirementZeroChecks (clearBoxCount boxes slot) rest
  | _ :: _ => False

theorem prepared_clear_box_counts (active : Activation) (code : Code) (slot : Nat) :
    (fun index => (((active.forgetRefs code).state.set slot .empty) index).dropWork.boxes) =
      clearBoxCount (fun index => (active.state index).dropWork.boxes) slot := by
  funext index
  by_cases same : index = slot
  · simp only [Partial.Locals.set, clearBoxCount, same, ite_true, Slot.dropWork]
  · simp only [Partial.Locals.set, clearBoxCount, same, ite_false]
    exact Activation.forgetRefs_boxes active code index

theorem RetirementPlan.complete_fresh {before : World} {callers : List Activation} {previous : Resources}
    {external exceptions : List Nat} (callee : Derived.Callees) (suffix : Code)
    {roots finalRoots : Roots} {actions : List Action} (plan : RetirementPlan roots actions finalRoots) :
    ∀ {world : World} {active : Activation}, OriginalLoanMachine before callers previous external exceptions world active →
      active.roots = roots → (∀ index ∈ exceptions, index < active.count) →
      (∀ slot, Action.drop slot ∈ actions ∨ Action.storageDead slot ∈ actions → LocalOwnersAbove before.memory.length world active slot) →
      retirementZeroChecks (fun slot => (active.state slot).dropWork.boxes) actions →
      ∃ final after, Calling.Prefix callee callers suffix actions world active final after ∧
        OriginalLoanMachine before callers previous external exceptions final after ∧ after.roots = finalRoots ∧
        after.count = active.count ∧ final.memory = world.memory := by
  induction plan with
  | nil roots =>
    intro world active machine rootsEq bounded fresh zero
    exact ⟨world, active, .nil _ _, machine, rootsEq, rfl, rfl⟩
  | @drop roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq bounded fresh zero
    let code := (Action.drop slot :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have ready := machine.prepare code
    have root : prepared.roots slot = some binding := by change active.roots slot = _; rw [rootsEq]; exact bound
    obtain ⟨discarded, run, length, next⟩ := ready.drop_fresh root bounded
      ((fresh slot (Or.inl (by simp))).prepare_any code)
    have nextFresh : ∀ index, Action.drop index ∈ rest ∨ Action.storageDead index ∈ rest →
        LocalOwnersAbove before.memory.length (world.retire discarded) {prepared with state := prepared.state.set slot .empty} index := by
      intro index member
      by_cases same : index = slot
      · subst index; exact LocalOwnersAbove.of_zero (by simp only [Partial.Locals.set, ite_true, Slot.dropWork])
      · exact ((fresh index (member.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _))).prepare_any code).memory_same
          ready.native.valid rfl rfl (by simp only [Partial.Locals.set, same, ite_false]; rfl)
    have nextZero : retirementZeroChecks
        (fun index => (({prepared with state := prepared.state.set slot .empty} : Activation).state index).dropWork.boxes) rest := by
      rw [prepared_clear_box_counts]
      exact zero
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter, memoryAfter⟩ :=
      ih next rootsEq bounded nextFresh nextZero
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .drop slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter, memoryAfter⟩
  | @dead roots finalRoots slot binding rest bound tail ih =>
    intro world active machine rootsEq bounded fresh zero
    let code := (Action.storageDead slot :: rest).foldr Control.Tree.step suffix
    let prepared := active.forgetRefs code
    have ready := machine.prepare code
    have root : prepared.roots slot = some binding := by change active.roots slot = _; rw [rootsEq]; exact bound
    obtain ⟨run, next⟩ := ready.storageDead root (prepare_zero_work code active zero.1)
    have nextFresh : ∀ index, Action.drop index ∈ rest ∨ Action.storageDead index ∈ rest →
        LocalOwnersAbove before.memory.length (world.retire [binding.address])
          {prepared with roots := prepared.roots.set slot none, state := prepared.state.set slot .empty} index := by
      intro index member
      exact Derived.storageDead_owner_provenance ready.native.valid ready.native.callersValid ready.native.wellFormed run index
        ((fresh index (member.imp (List.mem_cons_of_mem _) (List.mem_cons_of_mem _))).prepare_any code)
    have nextZero : retirementZeroChecks
        (fun index => (({prepared with roots := prepared.roots.set slot none, state := prepared.state.set slot .empty} : Activation).state index).dropWork.boxes) rest := by
      rw [prepared_clear_box_counts]
      exact zero.2
    obtain ⟨final, after, prefixRun, machineAfter, rootsAfter, countAfter, memoryAfter⟩ :=
      ih next (by change active.roots.set slot none = roots.set slot none; rw [rootsEq]) bounded nextFresh nextZero
    exact ⟨final, after, .cons (Calling.instruction_noncall_run (act := .storageDead slot) run) prefixRun,
      machineAfter, rootsAfter, countAfter, memoryAfter⟩

end SubtreeProofs.Rust.SourceEval.Addressed
