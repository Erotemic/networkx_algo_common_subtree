module

public import SubtreeProofs.Rust.SourceTypedPrefixes
public import SubtreeProofs.Rust.SourcePrefixOwnerProvenance
public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Recover moved-out and nonowning cleanup masks from successful instructions.
Reference preparation preserves the number of owned cells even when it ends a
shared view. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval

open LookupSource Heap Partial

theorem action_move_local_empty {call : Calls} {state after : State} {cost : Cost} {source destination : Nat}
    (different : source ≠ destination)
    (run : action call state (.assign destination (.use (.move (.local source)))) = some (after, cost)) :
    after source = .empty := by
  simp only [action, expression, operand, bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨value, middle⟩, moved, same⟩ := run
  cases same
  obtain ⟨_, remaining, rfl, hole, _⟩ := Partial.Locals.move_spec moved
  simp only [splitPlace, Slot.get, Option.some.injEq] at hole
  subst remaining
  simp only [Partial.Locals.set, splitPlace, different, ite_false, ite_true]

theorem optional_take_hole {part after : Slot} {value : Value}
    (typed : SlotTyped part (.adt .optional))
    (run : part.take [.field (some 1) 0] = some (value, after)) :
    after = .node .optional 1 [.empty] := by
  cases typed with
  | empty => simp [Slot.take] at run
  | node shape fields =>
    cases shape with
    | none => simp [Slot.take] at run
    | some =>
      cases fields with
      | cons first rest =>
        cases rest
        simp only [Slot.take, Option.all_some, decide_true, ite_true, List.getElem?_cons_zero,
          bind, Option.bind_eq_some_iff] at run
        obtain ⟨child, selected, moved, taken, same⟩ := run
        cases selected
        obtain ⟨result, materialized, taken⟩ := taken
        cases taken
        cases same
        rfl

theorem action_optional_move_hole {call : Calls} {state after : State} {cost : Cost} {source destination : Nat}
    (different : source ≠ destination) (typed : SlotTyped (state source) (.adt .optional))
    (run : action call state (.assign destination (.use (.move (.field (.local source) (some 1) 0)))) = some (after, cost)) :
    after source = .node .optional 1 [.empty] := by
  simp only [action, expression, operand, bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨value, middle⟩, moved, same⟩ := run
  cases same
  simp only [Partial.Locals.move, splitPlace, List.nil_append, bind, Option.bind_eq_some_iff] at moved
  obtain ⟨⟨result, remaining⟩, taken, same⟩ := moved
  cases same
  rw [optional_take_hole typed taken]
  simp only [Partial.Locals.set, different, ite_false, ite_true]

theorem action_copy_local_zero {call : Calls} {state after : State} {cost : Cost} {source destination : Nat}
    (different : source ≠ destination)
    (run : action call state (.assign destination (.use (.copy (.local source)))) = some (after, cost)) :
    (after source).dropWork.boxes = 0 := by
  simp only [action, expression, bind, Option.bind_eq_some_iff] at run
  obtain ⟨⟨value, middle⟩, copied, same⟩ := run
  cases same
  obtain ⟨sameMiddle, read, zero⟩ := copy_nonowning copied
  rw [sameMiddle]
  have materialized : (state source).materialize = some value := by
    simpa only [Partial.Locals.read, splitPlace, Slot.read, Slot.get, bind, Option.bind] using read
  simpa only [Partial.Locals.set, different, ite_false, Slot.eq_of_materialize _ materialized] using zero

end SubtreeProofs.Rust.SourceEval

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem Prefix.boxes_same_calls {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after) {slot : Nat}
    (safe : actions.all (LocalPreservation.action slot) = true) :
    (after.state slot).dropWork.boxes = (active.state slot).dropWork.boxes := by
  induction steps with
  | nil => rfl
  | @cons world middle final active current after act rest cost run tail ih =>
    have all := List.all_eq_true.mp safe
    rw [ih (List.all_eq_true.mpr (fun instruction member => all instruction (List.mem_cons_of_mem _ member))),
      instruction_local_same slot (all act (by simp)) run]
    exact Activation.forgetRefs_boxes active _ slot

theorem Prefix.empty_untouched {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after) {slot : Nat}
    (empty : active.state slot = .empty) (safe : actions.all (LocalPreservation.action slot) = true) :
    after.state slot = .empty := by
  exact (steps.unshared_local_same_calls (by rw [empty]; intro value impossible; cases impossible) safe).trans empty

theorem Prefix.optional_hole_untouched {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {actions : List Action} {world final : World} {active after : Activation}
    (steps : Prefix callee callers suffix actions world active final after) {slot : Nat}
    (hole : active.state slot = .node .optional 1 [.empty]) (safe : actions.all (LocalPreservation.action slot) = true) :
    after.state slot = .node .optional 1 [.empty] := by
  exact (steps.unshared_local_same_calls (by rw [hole]; intro value impossible; cases impossible) safe).trans hole

theorem Prefix.typed_move_empty {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code}
    {before rest : List Action} {slot destination : Nat}
    (steps : Prefix callee callers suffix (before ++ .assign destination (.use (.move (.local slot))) :: rest)
      world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ before, Types.ActionConstraints locals act)
    (different : slot ≠ destination) (safe : rest.all (LocalPreservation.action slot) = true) :
    after.state slot = .empty := by
  obtain ⟨middle, current, earlier, later⟩ := steps.split
  have checked := earlier.typed_spec respects sourceTyped ha hc hw typed constraints
  cases later with
  | @cons _ next _ _ currentAfter _ _ _ cost run tail =>
    have first := noncall_spec (source := source) (Activation.forgetRefs_valid checked.1 _) checked.2.1 checked.2.2.1 _ run
    have empty := action_move_local_empty different first.source
    have preserved := tail.closed_local_same_calls (ty := .u32) (by rw [empty]; exact .empty _) .u32 safe
    exact preserved.trans empty

theorem Prefix.typed_optional_hole {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code}
    {before rest : List Action} {slot destination : Nat}
    (steps : Prefix callee callers suffix (before ++ .assign destination (.use (.move (.field (.local slot) (some 1) 0))) :: rest)
      world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ before, Types.ActionConstraints locals act)
    (slotType : locals[slot]? = some (.adt .optional))
    (different : slot ≠ destination) (safe : rest.all (LocalPreservation.action slot) = true) :
    after.state slot = .node .optional 1 [.empty] := by
  obtain ⟨middle, current, earlier, later⟩ := steps.split
  have checked := earlier.typed_spec respects sourceTyped ha hc hw typed constraints
  cases later with
  | @cons _ next _ _ currentAfter _ _ _ cost run tail =>
    have first := noncall_spec (source := source) (Activation.forgetRefs_valid checked.1 _) checked.2.1 checked.2.2.1 _ run
    have hole := action_optional_move_hole different
      (Activation.forgetRefs_typed checked.2.2.2 _ slot _ slotType) first.source
    have preserved := tail.unshared_local_same_calls (by rw [hole]; intro value impossible; cases impossible) safe
    exact preserved.trans hole

theorem Prefix.typed_copy_zero {callee : Derived.Callees} {source : Calls}
    (respects : CallsRespect callee source TypedReady) (sourceTyped : Types.CallsTyped source)
    {world final : World} {active after : Activation} {callers : List Activation} {suffix : Code}
    {before rest : List Action} {slot destination : Nat}
    (steps : Prefix callee callers suffix (before ++ .assign destination (.use (.copy (.local slot))) :: rest)
      world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    {locals : List Ty} (typed : LocalsTyped locals active.state)
    (constraints : ∀ act ∈ before, Types.ActionConstraints locals act)
    (different : slot ≠ destination) (safe : rest.all (LocalPreservation.action slot) = true) :
    (after.state slot).dropWork.boxes = 0 := by
  obtain ⟨middle, current, earlier, later⟩ := steps.split
  have checked := earlier.typed_spec respects sourceTyped ha hc hw typed constraints
  cases later with
  | @cons _ next _ _ currentAfter _ _ _ cost run tail =>
    have first := noncall_spec (source := source) (Activation.forgetRefs_valid checked.1 _) checked.2.1 checked.2.2.1 _ run
    exact (tail.boxes_same_calls safe).trans (action_copy_local_zero different first.source)

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
