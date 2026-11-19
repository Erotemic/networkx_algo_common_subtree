module

public import SubtreeProofs.Rust.SourceEmptyWitness

/-! Open insertion-result/table-argument storage and move the actual owned table
into the insertion argument. Original tuple/query loans permit aliases with
owned table data while the selected stack-root guard remains checked. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_table_transfer_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (inputs : InputLocals left right table active.state)
    (tuple : active.state 13 = queryTuple left right) (witness : active.state 16 = Slot.ofValue (encodeResult emptyWitness))
    (count : 20 ≤ active.count) (unbound18 : active.roots 18 = none) (unbound19 : active.roots 19 = none) :
    ∃ (final : World) (after : Activation) (root18 root19 : Binding),
      Calling.Prefix callee callers (emptyCode 10) ((emptyActions.drop 7).take 3) world active final after ∧
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧ after.count = active.count ∧
      after.roots 18 = some root18 ∧ after.roots 19 = some root19 ∧
      (∀ slot, slot ≠ 18 → slot ≠ 19 → after.roots slot = active.roots slot) ∧
      after.state 18 = .empty ∧ final.memory[root18.address]? = some (.node .tuple 0 []) ∧
      after.state 19 = Slot.ofValue (encodeTable table) ∧ after.state 3 = .empty ∧
      after.state 1 = .shared (encodeWord left) ∧ after.state 2 = .shared (encodeWord right) ∧
      after.state 13 = queryTuple left right ∧ after.state 16 = Slot.ofValue (encodeResult emptyWitness) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let p7 := active.forgetRefs (emptyCode 7)
  have m7 := h.prepare (emptyCode 7)
  have i7 := inputs.prepare_empty 7 (by decide)
  let root18 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w18 := world.allocate (.stack p7.frame 18 world.memory.length) (.node .tuple 0 [])
  let a18 : Activation := {p7 with roots := p7.roots.set 18 (some root18), state := p7.state.set 18 .empty}
  obtain ⟨live18, m18⟩ := m7.storageLive (slot := 18) (by change 18 < active.count; omega) unbound18 (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w18 a18 at m18
  have i18 : InputLocals left right table a18.state := i7.set 18 .empty (by decide)
  let p8 := a18.forgetRefs (emptyCode 8)
  have m8 := m18.prepare (emptyCode 8)
  have i8 := i18.prepare_empty 8 (by decide)
  let root19 : Binding := ⟨w18.memory.length, w18.memory.length⟩
  let w19 := w18.allocate (.stack p8.frame 19 w18.memory.length) (.node .tuple 0 [])
  let a19 : Activation := {p8 with roots := p8.roots.set 19 (some root19), state := p8.state.set 19 .empty}
  obtain ⟨live19, m19⟩ := m8.storageLive (slot := 19) (by change 19 < active.count; omega)
    (by simpa [p8, a18, p7, Roots.set, Activation.forgetRefs] using unbound19) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w19 a19 at m19
  have i19 : InputLocals left right table a19.state := i8.set 19 .empty (by decide)
  let p9 := a19.forgetRefs (emptyCode 9)
  have m9 := m19.prepare (emptyCode 9)
  have i9 := i19.prepare_empty 9 (by decide)
  have bound19 : p9.roots 19 = some root19 := by simp [p9, a19, Roots.set, Activation.forgetRefs]
  have bound18 : p9.roots 18 = some root18 := by simp [p9, a19, p8, a18, Roots.set, Activation.forgetRefs]
  have empty19 : (p9.state.set 3 .empty) 19 = .empty := by
    simp only [Partial.Locals.set, show (19 : Nat) ≠ 3 by decide, ite_false]
    rw [m19.prepare_closed_local _ 19 (by decide)]
    simp only [a19, Partial.Locals.set, ite_true]
  obtain ⟨cell19, assign19, finalMachine⟩ := m9.assign_empty bound19 (by decide) (w18.allocate_spec _ _).2.1
    (use_local_source (by rw [i9.table]; exact Slot.materialize_ofValue _)) empty19 (m9.closed.clear 3)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set]) trivial (table_typed table) (.adt .table)
  let final := w19.write root19.address cell19
  let after : Activation := {p9 with state := (p9.state.set 3 .empty).set 19 (Slot.ofValue (encodeTable table))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] final after at finalMachine
  have whole : Calling.Prefix callee callers (emptyCode 10) ((emptyActions.drop 7).take 3) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 18) live18)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 19) live19)
        (.cons (Calling.instruction_noncall_run (act := .assign 19 (.use (.move (.local 3)))) assign19) (.nil _ _)))
  have raw18w19 : w19.memory[root18.address]? = some (.node .tuple 0 []) :=
    (w18.allocate_keeps m18.native.wellFormed _ _ []).memory _ _ (world.allocate_spec _ _).2.1
  refine ⟨final, after, root18, root19, whole, finalMachine, rfl, bound18, bound19, ?_, ?_,
    Activation.write_other_root m9.native.valid bound19 bound18 (by decide) raw18w19 cell19,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot eighteen nineteen
    simp only [after, p9, a19, p8, a18, p7, Activation.forgetRefs, Roots.set, eighteen, nineteen, ite_false]
  · simp only [after, Partial.Locals.set, show (18 : Nat) ≠ 19 by decide, show (18 : Nat) ≠ 3 by decide, ite_false]
    rw [m19.prepare_closed_local _ 18 (by decide)]
    simp only [a19, Partial.Locals.set, show (18 : Nat) ≠ 19 by decide, ite_false]
    rw [m18.prepare_closed_local _ 18 (by decide)]
    simp only [a18, Partial.Locals.set, ite_true]
  · simp only [after, Partial.Locals.set, ite_true]
  · simp [after, Partial.Locals.set]
  · simpa [after, Partial.Locals.set] using i9.left
  · simpa [after, Partial.Locals.set] using i9.right
  · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple
  · exact (whole.closed_local_same (index := 16) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [witness]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans witness
  · intro slot binding root raw memory
    have eighteen : slot ≠ 18 := by intro same; subst slot; rw [unbound18] at root; cases root
    have nineteen : slot ≠ 19 := by intro same; subst slot; rw [unbound19] at root; cases root
    have currentRoot : p9.roots slot = some binding := by
      simpa only [p9, a19, p8, a18, p7, Activation.forgetRefs, Roots.set, eighteen, nineteen, ite_false] using root
    have raw18 : w18.memory[binding.address]? = some raw := (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ memory
    have raw19 : w19.memory[binding.address]? = some raw := (w18.allocate_keeps m18.native.wellFormed _ _ []).memory _ _ raw18
    exact Activation.write_other_root m9.native.valid bound19 currentRoot (Ne.symm nineteen) raw19 cell19

end SubtreeProofs.Rust.SourceEval.Evaluator
