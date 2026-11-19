module

public import SubtreeProofs.Rust.SourceEvalTypedRecursive
public import SubtreeProofs.Rust.SourcePrefixIdentity
public import SubtreeProofs.Rust.SourceFreshWritePrefixes
public import SubtreeProofs.Rust.SourceCallRootPreservation

/-! Actual finite prefixes inherit local typing from checked source actions.
This derives every call's readiness while retaining an untouched physical root,
including when the corresponding logical slot is empty. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap

theorem CodeConstraints.prefix {locals : List Ty} {output : Ty} {suffix : Code} {actions : List Action}
    (h : CodeConstraints locals output (actions.foldr Control.Tree.step suffix)) :
    (∀ act ∈ actions, ActionConstraints locals act) ∧ CodeConstraints locals output suffix := by
  induction actions with
  | nil => exact ⟨by simp, h⟩
  | cons act rest ih =>
    cases h with
    | step first tail =>
      obtain ⟨all, last⟩ := ih tail
      exact ⟨fun instruction member => by
        rcases List.mem_cons.mp member with rfl | remaining
        · exact first
        · exact all instruction remaining, last⟩

theorem CodeConstraints.branches {locals : List Ty} {output : Ty} {scrut : Scrutinee}
    {branches : List (Key × Nat)} {fallback : Option Nat} {yes no rest : Code}
    (h : CodeConstraints locals output (.switch scrut branches fallback yes no rest)) :
    CodeConstraints locals output yes ∧ CodeConstraints locals output no ∧ CodeConstraints locals output rest := by
  cases h with
  | switch _ _ left right tail => exact ⟨left, right, tail⟩

end SubtreeProofs.Rust.SourceEval.Types

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem instruction_other_root {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady)
    {world final : World} {active after : Activation} {callers : List Activation} {act : Action} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (ready : ReadyAt TypedReady world active callers act)
    (run : instruction callee callers (world, active) act = some ((final, after), cost))
    {slot : Nat} {binding : Binding} {raw : Cell} (root : active.roots slot = some binding)
    (read : world.memory[binding.address]? = some raw) (different : LoanEnding.writes act ≠ some slot) :
    final.memory[binding.address]? = some raw := by
  cases act with
  | call function args destination =>
    simp only [instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state, inner⟩, called, same⟩ := run
    cases same
    have other : slot ≠ destination := by intro same; subst slot; exact different rfl
    exact (Derived.call_preserves_other_root respects ha hc hw function args destination ready called other root).reads
      binding.address (by simp) raw read
  | storageLive destination =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    simp only [Derived.action, Derived.storageLive] at acted
    split at acted
    next accepted =>
      simp only [bind, Option.bind_eq_some_iff] at acted
      obtain ⟨current, scanned, suspended, callerScan, last⟩ := acted
      cases last
      exact (world.allocate_keeps hw _ _ []).memory _ _ read
    next => cases acted
  | storageDead destination =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    have checked := Derived.storageDead_spec ha hc hw acted
    obtain ⟨_, _, retired, _⟩ := checked.2.2.2.2
    rw [retired]; exact read
  | assign destination rhs =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    obtain ⟨target, cell, bound, written⟩ := Derived.assign_world acted
    have other : destination ≠ slot := by intro same; subst destination; exact different rfl
    rw [written]
    exact Evaluator.Activation.write_other_root ha bound root other read cell
  | drop destination =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    have checked := Derived.drop_spec ha hc hw acted
    obtain ⟨_, _, _, _, retired, _⟩ := checked.2.2.2
    rw [retired]; exact read
  | fakeRead place =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    cases acted; exact read
  | undefinedBehavior =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, same⟩ := run
    cases same
    cases acted

theorem Prefix.typed_spec {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code} {actions : List Action}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ actions, Types.ActionConstraints locals act) :
    after.Valid final ∧ (∀ caller ∈ callers, caller.Valid final) ∧ final.WellFormed ∧ LocalsTyped locals after.state := by
  induction steps with
  | nil => exact ⟨ha, hc, hw, typed⟩
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    have valid := Activation.forgetRefs_valid ha code
    have prepared := Activation.forgetRefs_typed typed code
    have ready := readyAt_typed (callers := callers) valid prepared act (constraints act (by simp))
    have checked := instruction_spec respects valid hc hw act ready run
    exact ih checked.valid checked.callers checked.wellFormed
      (Types.action_typed sourceTyped prepared act (constraints act (by simp)) checked.source)
      (fun instruction member => constraints instruction (List.mem_cons_of_mem _ member))

theorem Prefix.typed_other_root {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code} {actions : List Action}
    (steps : Prefix callee callers suffix actions world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ actions, Types.ActionConstraints locals act)
    {slot : Nat} {binding : Binding} {raw : Cell} (root : active.roots slot = some binding)
    (read : world.memory[binding.address]? = some raw)
    (unchanged : ∀ act ∈ actions, LoanEnding.writes act ≠ some slot) :
    after.roots slot = some binding ∧ final.memory[binding.address]? = some raw := by
  induction steps with
  | nil => exact ⟨root, read⟩
  | @cons world middle final active current after act rest cost run tail ih =>
    let code := (act :: rest).foldr Control.Tree.step suffix
    have valid := Activation.forgetRefs_valid ha code
    have prepared := Activation.forgetRefs_typed typed code
    have ready := readyAt_typed (callers := callers) valid prepared act (constraints act (by simp))
    have checked := instruction_spec respects valid hc hw act ready run
    have memory := instruction_other_root respects valid hc hw ready run root read (unchanged act (by simp))
    have notWritten := unchanged act (by simp)
    have keeps : keepsRoot slot act := by
      cases act <;> first | trivial | intro same; subst slot; exact notWritten rfl
    have rootNow : current.roots slot = some binding :=
      ((instruction_shape run).2.2 slot keeps).trans root
    exact ih checked.valid checked.callers checked.wellFormed
      (Types.action_typed sourceTyped prepared act (constraints act (by simp)) checked.source)
      (fun instruction member => constraints instruction (List.mem_cons_of_mem _ member)) rootNow memory
      (fun instruction member => unchanged instruction (List.mem_cons_of_mem _ member))

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
