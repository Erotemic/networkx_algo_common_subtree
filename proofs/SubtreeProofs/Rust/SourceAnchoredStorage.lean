module

public import SubtreeProofs.Rust.SourceAnchoredBorrow

/-! Opening unrelated stack storage preserves a precise owned-word loan
anchor, the original query origins and the supported fresh references. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem AnchoredLoanMachine.storageLive {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external original fresh : List Nat} {source : Nat} {word : BalancedWord} {anchor : Resources}
    (h : AnchoredLoanMachine before callers previous external original fresh source word anchor world active)
    {slot : Nat} (bound : slot < active.count) (unbound : active.roots slot = none)
    (outside : slot ∉ fresh ++ original) (different : source ≠ slot) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    Derived.storageLive world active callers slot = some (final, after) ∧
      AnchoredLoanMachine before callers previous external original fresh source word anchor final after := by
  dsimp only
  obtain ⟨run, native⟩ := h.native.storageLive bound unbound
  refine ⟨run, ⟨native, h.closed.clear slot, ?_, ?_, ?_, ?_, ?_, h.sourceBound⟩⟩
  · intro index member
    have other : index ≠ slot := by intro same; subst index; exact outside member
    simpa only [Partial.Locals.set, other, ite_false] using h.zero index member
  · intro index member
    have other : index ≠ slot := by intro same; subst index; exact outside (List.mem_append_right fresh member)
    exact ((h.origins index member).allocate h.native.wellFormed _ _).congr
      (after := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty})
      rfl (by simp only [Roots.set, other, ite_false]) (by simp only [Partial.Locals.set, other, ite_false])
  · intro index member
    have other : index ≠ slot := by intro same; subst index; exact outside (List.mem_append_left original member)
    exact ((h.supportedLoans index member).allocate h.native.wellFormed _ _).congr
      (after := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty})
      rfl (by simp only [Roots.set, other, ite_false]) (by simp only [Partial.Locals.set, other, ite_false])
  · exact (h.owning.transport (world.allocate_keeps h.native.wellFormed _ _ anchor.reads).preserves).congr_at
      (by simp only [Roots.set, different, ite_false]) (by simp only [Partial.Locals.set, different, ite_false])
  · simpa only [Partial.Locals.set, different, ite_false] using h.value

end SubtreeProofs.Rust.SourceEval.Addressed
