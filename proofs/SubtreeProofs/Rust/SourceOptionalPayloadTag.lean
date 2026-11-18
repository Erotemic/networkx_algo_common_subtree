module

public import SubtreeProofs.Rust.SourcePrefixMaskFacts
public import SubtreeProofs.Rust.SourceScrutineeTotality

/-! A constructed payload read certifies the earlier optional switch tag.
This reflects finite successful instructions, not a whole-parent execution. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource Heap Partial

theorem optional_read_node {part : Slot} {ty : Ty} {value : Value}
    (optional : ty = .adt .optional ∨ ∃ inner, ty = .option inner)
    (typed : SlotTyped part ty)
    (read : part.read [.field (some 1) 0] = some value) :
    ∃ fields, part = .node .optional 1 fields := by
  rcases optional with rfl | ⟨inner, rfl⟩
  all_goals
    cases typed with
    | empty => simp [Slot.read, Slot.get] at read
    | node shape fields =>
      cases shape <;> first
        | exact ⟨_, rfl⟩
        | simp [Slot.read, Slot.get] at read

end SubtreeProofs.Rust.SourceEval

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem Prefix.typed_payload_tag {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code}
    {before rest : List Action} {slot destination : Nat} {op : Operand}
    (steps : Prefix callee callers suffix (before ++ .assign destination (.use op) :: rest) world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ before, Types.ActionConstraints locals act)
    {ty : Ty} (slotType : locals[slot]? = some ty)
    (optional : ty = .adt .optional ∨ ∃ inner, ty = .option inner) (closed : Borrow.Closed ty)
    (safe : before.all (LocalPreservation.action slot) = true)
    (reads : ∀ state value remaining, SourceEval.operand state op = some (value, remaining) →
      state.read (.field (.local slot) (some 1) 0) = some value) :
    Derived.scrutinee world active callers (.discriminant (.local slot)) = some (.variant .optional 1, active) := by
  obtain ⟨middle, current, earlier, later⟩ := steps.split
  have checked := earlier.typed_spec respects sourceTyped ha hc hw typed constraints
  have unchanged := earlier.closed_local_same_calls (typed slot _ slotType) closed safe
  cases later with
  | @cons _ next _ _ currentAfter _ _ _ cost run tail =>
    let code := (.assign destination (.use op) :: rest).foldr Control.Tree.step suffix
    have first := noncall_spec (source := source) (Activation.forgetRefs_valid checked.1 _) checked.2.1 checked.2.2.1 _ run
    have actual := first.source
    simp only [SourceEval.action, bind, Option.bind_eq_some_iff] at actual
    obtain ⟨⟨value, masks⟩, operandRun, last⟩ := actual
    have preparedTyped := Activation.forgetRefs_typed checked.2.2.2 code slot _ slotType
    obtain ⟨fields, tagged⟩ := optional_read_node optional preparedTyped (reads _ _ _ operandRun)
    have same : (current.forgetRefs code).state slot = active.state slot :=
      (LoanEnding.forget_closed _ _ (checked.2.2.2 slot _ slotType) closed).trans unchanged
    rw [same] at tagged
    simpa only using Derived.scrutinee_complete ha hc (.discriminant (.local slot))
      (by simp [SourceEval.scrutinee, splitPlace, tagged, Slot.get]) (by intros; trivial)

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
