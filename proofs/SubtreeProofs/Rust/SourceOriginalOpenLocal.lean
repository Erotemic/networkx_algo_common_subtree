module

public import SubtreeProofs.Rust.SourceOriginalLoanMachine

/-! Open one actual empty local while retaining original loan families and all
older root bytes. The allocated stack root remains explicit for later stores. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_open_local_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    {slot : Nat} (outside : slot ∉ exceptions) (bound : slot < active.count) (unbound : active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive slot] world active final after ∧
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧ after.state slot = .empty ∧
      final.memory[world.memory.length]? = some (.node .tuple 0 []) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let code : SourceEval.Code := .step (.storageLive slot) suffix
  let prepared := active.forgetRefs code
  have machine := h.prepare code
  obtain ⟨run, finalMachine⟩ := machine.storageLive bound unbound outside
  refine ⟨_, _, .cons (Calling.instruction_noncall_run (act := .storageLive slot) run) (.nil _ _),
    finalMachine, rfl, rfl, rfl, ?_, (world.allocate_spec _ _).2.1, ?_⟩
  · simp only [Partial.Locals.set, ite_true]
  · intro index binding root raw memoryRead
    exact (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memoryRead

end SubtreeProofs.Rust.SourceEval.Addressed
