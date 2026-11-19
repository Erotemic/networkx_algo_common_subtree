module

public import SubtreeProofs.Rust.SourceRetainedOwnerProvenance
public import SubtreeProofs.Rust.SourceResultOwnerProvenance
public import SubtreeProofs.Rust.SourcePrefixIdentity

/-! Owner bounds follow actual continuation-aware primitive prefixes. A finite
transfer plan names source locals and maintained source mutation facts; the
existing instruction executor supplies all physical moves and stores. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LocalOwnersAbove.prepare_any {bound : Nat} {world : World} {active : Activation} {slot : Nat}
    (above : LocalOwnersAbove bound world active slot) (code : Code) :
    LocalOwnersAbove bound world (active.forgetRefs code) slot := by
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
  · intro resources represented address member
    exact above resources (represented.congr_at rfl same.symm) address member
  · exact LocalOwnersAbove.of_zero (by change (LoanEnding.forget code _ _ slot).dropWork.boxes = 0; rw [empty]; simp only [Slot.dropWork])

theorem LocalOwnersAbove.memory_same {bound : Nat} {world final : World} {active after : Activation} {slot : Nat}
    (ha : active.Valid world) (above : LocalOwnersAbove bound world active slot)
    (memory : final.memory = world.memory) (roots : after.roots slot = active.roots slot)
    (masks : after.state slot = active.state slot) : LocalOwnersAbove bound final after slot := by
  obtain ⟨_, guards, frame⟩ := ha
  obtain ⟨old, _, represented⟩ := frame.inspectSlot slot
  intro actual actualRep address member
  have raw : rawAt final after.roots slot = rawAt world active.roots slot := by simp only [rawAt, roots, memory]
  have same : actual.owners = old.owners := by
    rw [← actualRep.source.ownerList]
    rw [memory, raw, masks]
    exact represented.source.ownerList
  exact above old represented address (same ▸ member)

namespace Derived

theorem storageDead_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {slot : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (run : storageDead world active callers slot = some (final, after)) :
    ∀ index, LocalOwnersAbove bound world active index → LocalOwnersAbove bound final after index := by
  have spec := storageDead_spec ha hc hw run
  obtain ⟨binding, _, retired, _⟩ := spec.2.2.2.2
  intro index above
  by_cases same : index = slot
  · subst index
    exact LocalOwnersAbove.of_zero (by rw [spec.2.2.1]; simp [Partial.Locals.set, Slot.dropWork])
  · exact above.memory_same ha (by rw [retired]; rfl)
      (by rw [spec.2.1]; simp [Roots.set, same]) (by rw [spec.2.2.1]; simp [Partial.Locals.set, same])

theorem action_keeps_owner_provenance {bound : Nat} {world final : World} {active after : Activation}
    {callers : List Activation} {act : Action} {index : Nat}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (safe : LocalPreservation.action index act = true) (above : LocalOwnersAbove bound world active index)
    (run : action world active callers act = some (final, after)) : LocalOwnersAbove bound final after index := by
  by_cases bounded : index < active.count
  · cases act with
    | storageLive slot => exact storageLive_owner_provenance ha hw run index above
    | storageDead slot => exact storageDead_owner_provenance ha hc hw run index above
    | assign slot rhs => exact assign_keeps_owner_provenance ha hc hw bounded safe above run
    | drop slot => exact drop_keeps_owner_provenance ha hc hw (of_decide_eq_true safe) bounded above run
    | fakeRead place => cases run; exact above
    | call _ _ _ | undefinedBehavior => cases run
  · have root : active.roots index = none := ha.1 index (by omega)
    obtain ⟨_, frame⟩ := ha.2
    have empty : active.state index = .empty := by simpa only [root] using frame.slots index
    exact LocalOwnersAbove.of_zero (by rw [(action_local_same index safe run).trans empty]; simp only [Slot.dropWork])

end Derived

/-- Each assignment transfers owners only from the named local. Kept actions
use the existing source mutation certificate and exclude calls explicitly. -/
inductive OwnerTransfer : Nat → List Action → Nat → Prop where
  | nil (slot : Nat) : OwnerTransfer slot [] slot
  | keep {source destination : Nat} {act : Action} {rest : List Action}
      (noncall : Calling.noCalls (.step act .done) = true)
      (safe : LocalPreservation.action source act = true)
      (tail : OwnerTransfer source rest destination) : OwnerTransfer source (act :: rest) destination
  | assign {source slot destination : Nat} {rhs : Expr} {rest : List Action}
      (selected : ∀ bound world active, LocalOwnersAbove bound world active source → ExpressionSourcesAbove bound world active rhs)
      (tail : OwnerTransfer slot rest destination) : OwnerTransfer source (.assign slot rhs :: rest) destination

namespace Calling

theorem Prefix.owner_transfer {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation} {source destination bound : Nat}
    (plan : OwnerTransfer source actions destination)
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (above : LocalOwnersAbove bound world active source) : LocalOwnersAbove bound final after destination := by
  induction plan generalizing world active with
  | nil => cases steps; exact above
  | @keep source destination act rest noncall safe tail ih =>
    cases steps with
    | @cons _ middle _ _ current _ _ _ cost run more =>
      let prepared := active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)
      have valid := Activation.forgetRefs_valid ha ((act :: rest).foldr Control.Tree.step suffix)
      have acted : Derived.action world prepared callers act = some (middle, current) := by
        cases act <;> try cases noncall
        all_goals simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
        all_goals obtain ⟨⟨w, a⟩, acted, last⟩ := run; cases last; exact acted
      have checked := Derived.action_spec valid hc hw act acted
      exact ih more checked.valid checked.callers checked.wellFormed
        (Derived.action_keeps_owner_provenance valid hc hw safe (above.prepare_any _) acted)
  | @assign source slot destination rhs rest selected tail ih =>
    cases steps with
    | @cons _ middle _ _ current _ _ _ cost run more =>
      let code := (Action.assign slot rhs :: rest).foldr Control.Tree.step suffix
      have valid := Activation.forgetRefs_valid ha code
      have acted : Derived.assign world (active.forgetRefs code) callers slot rhs = some (middle, current) := by
        simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
        obtain ⟨⟨w, a⟩, acted, last⟩ := run
        cases last
        exact acted
      have checked := Derived.action_spec valid hc hw (.assign slot rhs) acted
      exact ih more checked.valid checked.callers checked.wellFormed
        (Derived.assign_owner_provenance valid (selected _ _ _ (above.prepare_any code)) acted)

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.split {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {first rest : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix (first ++ rest) world active final after) :
    ∃ middle current, Prefix callee callers (rest.foldr Control.Tree.step suffix) first world active middle current ∧
      Prefix callee callers suffix rest middle current final after := by
  induction first generalizing world active with
  | nil => exact ⟨world, active, .nil _ _, steps⟩
  | cons act more ih =>
    cases steps with
    | @cons _ next _ _ current _ _ _ cost run tail =>
      obtain ⟨middle, interim, firstSteps, restSteps⟩ := ih tail
      refine ⟨middle, interim, .cons (cost := cost) ?_ firstSteps, restSteps⟩
      change instruction callee callers (world, active.forgetRefs (((act :: more) ++ rest).foldr Control.Tree.step suffix)) act = _ at run
      rw [List.foldr_append] at run
      exact run

theorem Prefix.noncall_valid {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (noCalls : Calling.noCalls (actions.foldr Control.Tree.step .done) = true) :
    after.Valid final ∧ (∀ caller ∈ callers, caller.Valid final) ∧ final.WellFormed := by
  induction steps with
  | nil => exact ⟨ha, hc, hw⟩
  | @cons world middle final active current after act rest cost run tail ih =>
    have noncall : Derived.instruction callers (world, active.forgetRefs ((act :: rest).foldr Control.Tree.step suffix)) act =
        some ((middle, current), cost) := by
      cases act <;> first | exact run | cases noCalls
    have checked := noncall_spec (source := fun _ _ => none) (Activation.forgetRefs_valid ha _) hc hw act noncall
    have tailNoCalls : Calling.noCalls (rest.foldr Control.Tree.step .done) = true := by
      cases act <;> first | exact noCalls | cases noCalls
    exact ih checked.valid checked.callers checked.wellFormed tailNoCalls

end SubtreeProofs.Rust.SourceEval.Addressed.Calling

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem LocalResultOwnersAbove.memory_same {bound : Nat} {world final : World} {active after : Activation} {slot : Nat}
    (above : LocalResultOwnersAbove bound world active slot)
    (memory : final.memory = world.memory) (roots : after.roots slot = active.roots slot) :
    LocalResultOwnersAbove bound final after slot := by
  obtain ⟨cell, raw, fresh⟩ := above
  refine ⟨cell, ?_, ?_⟩
  · simpa only [rawAt, roots, memory] using raw
  · rw [memory]; exact fresh

namespace Calling

theorem Prefix.retirement_memory {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (onlyRetire : ∀ act ∈ actions, ∃ slot, act = .drop slot ∨ act = .storageDead slot) : final.memory = world.memory := by
  induction steps with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    obtain ⟨slot, rfl | rfl⟩ := onlyRetire act (by simp)
    all_goals
      simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨w, a⟩, acted, last⟩ := run
      cases last
    · have checked := Derived.drop_spec (Activation.forgetRefs_valid ha _) hc hw acted
      obtain ⟨item, binding, _, _, retired, _⟩ := checked.2.2.2
      exact (ih checked.1.valid checked.1.callers checked.1.wellFormed
        (fun action member => onlyRetire action (List.mem_cons_of_mem _ member))).trans (by rw [retired]; rfl)
    · have checked := Derived.storageDead_spec (Activation.forgetRefs_valid ha _) hc hw acted
      obtain ⟨binding, _, retired, _⟩ := checked.2.2.2.2
      exact (ih checked.1.valid checked.1.callers checked.1.wellFormed
        (fun action member => onlyRetire action (List.mem_cons_of_mem _ member))).trans (by rw [retired]; rfl)

theorem Prefix.retirement_result_owner_provenance {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation} {bound slot : Nat}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (onlyRetire : ∀ act ∈ actions, ∃ index, act = .drop index ∨ act = .storageDead index)
    (keeps : ∀ act ∈ actions, keepsRoot slot act)
    (above : LocalResultOwnersAbove bound world active slot) : LocalResultOwnersAbove bound final after slot :=
  above.memory_same (steps.retirement_memory ha hc hw onlyRetire) (steps.shape.2.2 slot keeps)

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem Prefix.unique {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final next : World} {active after current : Activation}
    (first : Prefix callee callers suffix actions world active final after)
    (second : Prefix callee callers suffix actions world active next current) : final = next ∧ after = current := by
  induction first generalizing next current with
  | nil => cases second; exact ⟨rfl, rfl⟩
  | cons run tail ih =>
    cases second with
    | cons other rest =>
      have same := (Prod.mk.inj (Option.some.inj (run.symm.trans other))).1
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj same
      exact ih rest

theorem prefix_of_exec {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world : World} {active : Activation} {flow : Derived.Flow} {cost : Cost}
    (run : exec callee callers (actions.foldr Control.Tree.step suffix) world active = some (flow, cost)) :
    ∃ middle current last, Prefix callee callers suffix actions world active middle current ∧
      exec callee callers suffix middle current = some (flow, last) := by
  induction actions generalizing world active cost with
  | nil => exact ⟨world, active, cost, .nil _ _, run⟩
  | cons act rest ih =>
    rw [List.foldr_cons, exec_step] at run
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨⟨middle, current⟩, first⟩, acted, ⟨actual, last⟩, more, ending⟩ := run
    have same := (Prod.mk.inj (Option.some.inj ending)).1
    change actual = flow at same
    subst actual
    obtain ⟨final, after, work, steps, finalRun⟩ := ih more
    exact ⟨final, after, work, .cons acted steps, finalRun⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Calling

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem OperandSourcesAbove.single_move {bound source : Nat} {world : World} {active : Activation} {place : Place}
    (above : LocalOwnersAbove bound world active source) (root : (splitPlace place).1 = source) :
    OperandSourcesAbove bound world active [.move place] := by
  intro op member path same
  have selected : op = .move place := List.mem_singleton.mp member
  have eq := Operand.move.inj (same.symm.trans selected)
  cases eq
  rw [root]
  exact above

end SubtreeProofs.Rust.SourceEval.Addressed
