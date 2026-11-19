module

public import SubtreeProofs.Rust.SourcePrefixCallPreservation

/-! Opening a fresh local and assigning it preserves every older heap byte,
including cells of already retired locals. The fact follows from actual
allocation/store records and does not require a presumed post-step frame. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

namespace Derived

theorem store_world {world final : World} {roots : Roots} {frame destination : Nat} {retained : List Nat}
    {masks after : State} {packet : ValueCell}
    (run : store world roots frame destination retained masks packet = some (final, after)) :
    ∃ binding, roots destination = some binding ∧ final = world.write binding.address packet.1 := by
  simp only [store] at run
  split at run
  next empty =>
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨binding, root, used, traced, ending, written, result⟩ := run
    have same := (Prod.mk.inj (Option.some.inj result)).1
    exact ⟨binding, root, same.symm.trans (World.writeStack_iff.mp written).2.2.2.2⟩
  next => cases run

theorem assign_world {world final : World} {active after : Activation} {callers : List Activation}
    {destination : Nat} {rhs : Expr}
    (run : Derived.assign world active callers destination rhs = some (final, after)) :
    ∃ binding cell, active.roots destination = some binding ∧ final = world.write binding.address cell := by
  simp only [Derived.assign, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scan, suspended, callerScan, ⟨packet, masks⟩, expression, remainder, remaining,
    ⟨ending, state⟩, stored, run⟩ := run
  cases run
  obtain ⟨binding, root, finalEq⟩ := store_world stored
  exact ⟨binding, packet.1, root, finalEq⟩

end Derived

namespace Calling

theorem Prefix.open_assign_memory {callee : Derived.Callees} {callers : List Activation} {suffix : Code}
    {world final : World} {active after : Activation} {destination : Nat} {rhs : Expr}
    (h : Prefix callee callers suffix [.storageLive destination, .assign destination rhs] world active final after) :
    Heap.Extends world.memory final.memory := by
  cases h with
  | cons firstRun rest =>
    cases rest with
    | cons secondRun last =>
      cases last
      simp only [instruction, Derived.instruction, bind, Option.bind_eq_some_iff] at firstRun secondRun
      obtain ⟨⟨openedWorld, opened⟩, opening, sameFirst⟩ := firstRun
      cases sameFirst
      simp only [Derived.action, Derived.storageLive] at opening
      split at opening
      next ready =>
        simp only [bind, Option.bind_eq_some_iff] at opening
        obtain ⟨current, scan, suspended, callerScan, sameOpen⟩ := opening
        cases sameOpen
        obtain ⟨⟨ending, state⟩, assigning, sameLast⟩ := secondRun
        cases sameLast
        obtain ⟨binding, cell, atRoot, finalEq⟩ := Derived.assign_world assigning
        have rootEq : binding = ⟨world.memory.length, world.memory.length⟩ := by
          simpa only [Activation.forgetRefs, Roots.set, ite_true, Option.some.injEq] using atRoot.symm
        subst binding
        intro index raw memoryRead
        have small : index < world.memory.length := (List.getElem?_eq_some_iff.mp memoryRead).choose
        have different : world.memory.length ≠ index := by omega
        rw [finalEq]
        simpa only [World.write, World.allocate, List.getElem?_set_ne different, List.getElem?_append_left small] using memoryRead
      next => cases opening

end Calling
end SubtreeProofs.Rust.SourceEval.Addressed
