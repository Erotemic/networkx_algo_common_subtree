module

public import SubtreeProofs.Rust.SourceLocalPreservation
public import SubtreeProofs.Rust.SourceEvalCallingControl

/-! Raw addressed execution changes only the local masks named by the existing
source mutation certificates. These record-state facts require no callee
postcondition, readiness, ownership separation or successful parent invocation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem operand_local_same {world : World} {roots : Roots} {guarded : List Nat} {state after : State}
    {op : Operand} {packet : ValueCell} (index : Nat) (safe : LocalPreservation.operand index op = true)
    (run : Addressed.operand world roots guarded state op = some (packet, after)) : after index = state index := by
  cases op with
  | move place =>
    obtain ⟨pointer, moved, _, _⟩ := operand_move_iff.mp run
    exact Partial.Locals.move_other moved index (of_decide_eq_true safe)
  | copy place =>
    simp only [Addressed.operand, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨⟨cell, value⟩, pointer⟩, read, copied, copy, run⟩ := run
    cases run
    rfl
  | boolean value => cases run; rfl
  | number value =>
    simp only [Addressed.operand] at run
    split at run
    next => cases run; rfl
    next => cases run

theorem operands_local_same {world : World} {roots : Roots} {guarded : List Nat} {state after : State}
    {args : List Operand} {packets : List ValueCell} (index : Nat)
    (safe : LocalPreservation.operands index args = true)
    (run : Addressed.operands world roots guarded state args = some (packets, after)) : after index = state index := by
  induction args generalizing state packets with
  | nil => cases run; rfl
  | cons first rest ih =>
    have all := List.all_eq_true.mp safe
    simp only [Addressed.operands, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨packet, middle⟩, step, ⟨more, ending⟩, tail, run⟩ := run
    cases run
    exact (ih (List.all_eq_true.mpr (fun op member => all op (List.mem_cons_of_mem first member))) tail).trans
      (operand_local_same index (all first (by simp)) step)

theorem expression_local_same {world : World} {roots : Roots} {guarded : List Nat} {state after : State}
    {rhs : Expr} {packet : ValueCell} (index : Nat) (safe : LocalPreservation.expression index rhs = true)
    (run : Addressed.expression world roots guarded state rhs = some (packet, after)) : after index = state index := by
  cases rhs with
  | use op => exact operand_local_same index safe run
  | address place =>
    simp only [Addressed.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨value, read, cell, borrowed, run⟩ := run
    cases run
    rfl
  | aggregate kind tag args =>
    simp only [Addressed.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨packets, masks⟩, arguments, run⟩ := run
    cases run
    exact operands_local_same index safe arguments
  | less left right =>
    have parts := Bool.and_eq_true_iff.mp safe
    simp only [Addressed.expression, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨⟨leftCell, leftValue⟩, middle⟩, first, ⟨⟨rightCell, rightValue⟩, ending⟩, second, run⟩ := run
    have firstSame := operand_local_same index parts.1 first
    have secondSame := operand_local_same index parts.2 second
    cases leftCell <;> cases rightCell <;> try cases run
    simp only [Option.bind_eq_some_iff] at run
    obtain ⟨answer, _, run⟩ := run
    cases run
    exact secondSame.trans firstSame

namespace Derived

theorem store_state {world final : World} {roots : Roots} {frame destination : Nat} {retained : List Nat}
    {masks after : State} {packet : ValueCell}
    (run : store world roots frame destination retained masks packet = some (final, after)) :
    after = masks.set destination (Slot.ofValue packet.2) := by
  simp only [store] at run
  split at run
  next empty =>
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨binding, root, used, traced, ending, written, run⟩ := run
    exact (Prod.mk.inj (Option.some.inj run)).2.symm
  next => cases run

theorem assign_local_same {world final : World} {active after : Activation} {callers : List Activation}
    {destination : Nat} {rhs : Expr} (index : Nat)
    (safe : LocalPreservation.action index (.assign destination rhs) = true)
    (run : Derived.assign world active callers destination rhs = some (final, after)) : after.state index = active.state index := by
  have parts := Bool.and_eq_true_iff.mp safe
  simp only [Derived.assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packet, masks⟩, expression, remainder, remaining,
    ⟨ending, state⟩, stored, run⟩ := run
  cases run
  have unchanged := expression_local_same index parts.2 expression
  rw [store_state stored]
  simpa only [Partial.Locals.set, of_decide_eq_true parts.1, ite_false] using unchanged

theorem call_local_same {callee : Callees} {world final : World} {active after : Activation} {callers : List Activation}
    {function : Function} {args : List Operand} {destination : Nat} {cost : Cost} (index : Nat)
    (safe : LocalPreservation.action index (.call function args destination) = true)
    (run : Derived.call callee world active callers function args destination = some (final, after, cost)) : after.state index = active.state index := by
  have parts := Bool.and_eq_true_iff.mp safe
  simp only [Derived.call, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packets, masks⟩, arguments, remainder, remaining, binding, root,
    ⟨returned, packet, inner⟩, called, ⟨ending, state⟩, stored, run⟩ := run
  cases run
  have unchanged := operands_local_same index parts.2 arguments
  rw [store_state stored]
  simpa only [Partial.Locals.set, of_decide_eq_true parts.1, ite_false] using unchanged

theorem action_local_same {world final : World} {active after : Activation} {callers : List Activation} {act : Action}
    (index : Nat) (safe : LocalPreservation.action index act = true)
    (run : Derived.action world active callers act = some (final, after)) : after.state index = active.state index := by
  cases act with
  | storageLive destination =>
    simp only [Derived.action, storageLive] at run
    split at run
    next ready =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨current, scan, suspended, callerScan, run⟩ := run
      cases run
      simp only [Partial.Locals.set, of_decide_eq_true safe, ite_false]
    next => cases run
  | storageDead destination =>
    simp only [Derived.action, storageDead] at run
    split at run
    next zero =>
      simp only [bind, Option.bind_eq_some_iff] at run
      obtain ⟨⟨remainder, suspended⟩, context, binding, root, ending, ended, run⟩ := run
      cases run
      simp only [Partial.Locals.set, of_decide_eq_true safe, ite_false]
    next => cases run
  | assign destination rhs => exact assign_local_same index safe run
  | drop destination =>
    simp only [Derived.action, drop, bind, Option.bind_eq_some_iff] at run
    obtain ⟨item, inspected, ⟨remainder, suspended⟩, context, binding, root, run⟩ := run
    split at run
    next ready =>
      cases run
      simp only [Partial.Locals.set, of_decide_eq_true safe, ite_false]
    next => cases run
  | fakeRead place => cases run; rfl
  | call _ _ _ | undefinedBehavior => cases run

end Derived

namespace Calling

theorem instruction_local_same {callee : Derived.Callees} {world final : World} {active after : Activation}
    {callers : List Activation} {act : Action} {cost : Cost} (index : Nat)
    (safe : LocalPreservation.action index act = true)
    (run : instruction callee callers (world, active) act = some ((final, after), cost)) : after.state index = active.state index := by
  cases act with
  | call function args destination =>
    simp only [instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state, inner⟩, called, run⟩ := run
    cases run
    exact Derived.call_local_same index safe called
  | storageLive destination | storageDead destination | assign destination rhs | drop destination | fakeRead place | undefinedBehavior =>
    simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at run
    obtain ⟨⟨ending, state⟩, acted, run⟩ := run
    cases run
    exact Derived.action_local_same index safe acted

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
