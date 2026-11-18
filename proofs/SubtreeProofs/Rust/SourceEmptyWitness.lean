module

public import SubtreeProofs.Rust.SourceEmptyMissProgram
public import SubtreeProofs.Rust.SourcePrefixUnshared

/-! Construct the real empty witness without copying either query. Both fresh
locals, the two assignments, moved-word drop/retirement and fake-read execute
with the actual insertion/return continuation and original query-tuple loans. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_witness_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : MissScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 18 ≤ active.count) :
    ∃ (final : World) (after : Activation) (root16 : Binding),
      Calling.Prefix callee callers (emptyCode 7) (emptyActions.take 7) world active final after ∧
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧ InputLocals left right table after.state ∧
      after.count = active.count ∧ after.roots 16 = some root16 ∧ after.roots 17 = none ∧
      (∀ slot, slot ∉ [16, 17] → after.roots slot = active.roots slot) ∧
      after.state 16 = Slot.ofValue (encodeResult emptyWitness) ∧ after.state 13 = queryTuple left right ∧ after.state 0 = .empty ∧
      (∃ root0, after.roots 0 = some root0 ∧ final.memory[root0.address]? = some (.node .tuple 0 [])) := by
  obtain ⟨root0, bound0, raw0⟩ := scope.returnRoot
  let p0 := active.forgetRefs (emptyCode 0)
  have m0 := h.prepare (emptyCode 0)
  have i0 := scope.inputs.prepare_empty 0 (by decide)
  let root16 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w16 := world.allocate (.stack p0.frame 16 world.memory.length) (.node .tuple 0 [])
  let a16 : Activation := {p0 with roots := p0.roots.set 16 (some root16), state := p0.state.set 16 .empty}
  obtain ⟨live16, m16⟩ := m0.storageLive (slot := 16) (by change 16 < active.count; omega)
    (by change active.roots 16 = none; rw [scope.otherRoots 16 (by decide)]; exact unbound 16 (by decide)) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w16 a16 at m16
  have i16 : InputLocals left right table a16.state := i0.set 16 .empty (by decide)
  let p1 := a16.forgetRefs (emptyCode 1)
  have m1 := m16.prepare (emptyCode 1)
  have i1 := i16.prepare_empty 1 (by decide)
  let root17 : Binding := ⟨w16.memory.length, w16.memory.length⟩
  let w17 := w16.allocate (.stack p1.frame 17 w16.memory.length) (.node .tuple 0 [])
  let a17 : Activation := {p1 with roots := p1.roots.set 17 (some root17), state := p1.state.set 17 .empty}
  obtain ⟨live17, m17⟩ := m1.storageLive (slot := 17) (by change 17 < active.count; omega)
    (by simpa [p1, a16, p0, Roots.set, Activation.forgetRefs] using
      (scope.otherRoots 17 (by decide)).trans (unbound 17 (by decide))) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w17 a17 at m17
  have i17 : InputLocals left right table a17.state := i1.set 17 .empty (by decide)
  let p2 := a17.forgetRefs (emptyCode 2)
  have m2 := m17.prepare (emptyCode 2)
  have i2 := i17.prepare_empty 2 (by decide)
  have bound17 : p2.roots 17 = some root17 := by simp [p2, a17, Roots.set, Activation.forgetRefs]
  have bound16p2 : p2.roots 16 = some root16 := by simp [p2, a17, p1, a16, Roots.set, Activation.forgetRefs]
  have bound0p2 : p2.roots 0 = some root0 := by simpa [p2, a17, p1, a16, p0, Roots.set, Activation.forgetRefs] using bound0
  have empty17 : p2.state 17 = .empty := by
    rw [m17.prepare_closed_local _ 17 (by decide)]
    simp only [a17, Partial.Locals.set, ite_true]
  obtain ⟨cell17, assign17, ma17⟩ := m2.assign_empty bound17 (by decide) (w16.allocate_spec _ _).2.1
    (empty_word_source p2.state) empty17 m2.closed (by intro _ _; rfl) (by intro op member; cases member)
    (word_typed .Empty) (.adt .word)
  let wa17 := w17.write root17.address cell17
  let aa17 : Activation := {p2 with state := p2.state.set 17 (Slot.ofValue (encodeWord .Empty))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa17 aa17 at ma17
  have ia17 : InputLocals left right table aa17.state := i2.set 17 _ (by decide)
  have raw16w17 : w17.memory[root16.address]? = some (.node .tuple 0 []) :=
    (w16.allocate_keeps m16.native.wellFormed _ _ []).memory _ _ (world.allocate_spec _ _).2.1
  have raw0w16 : w16.memory[root0.address]? = some (.node .tuple 0 []) :=
    (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ raw0
  have raw0w17 : w17.memory[root0.address]? = some (.node .tuple 0 []) :=
    (w16.allocate_keeps m16.native.wellFormed _ _ []).memory _ _ raw0w16
  have raw16a17 := Activation.write_other_root m2.native.valid bound17 bound16p2 (by decide) raw16w17 cell17
  have raw0a17 := Activation.write_other_root m2.native.valid bound17 bound0p2 (by decide) raw0w17 cell17
  let p3 := aa17.forgetRefs (emptyCode 3)
  have m3 := ma17.prepare (emptyCode 3)
  have i3 := ia17.prepare_empty 3 (by decide)
  have ready17 : p3.state 17 = Slot.ofValue (encodeWord .Empty) := by
    rw [ma17.prepare_closed_local _ 17 (by decide)]
    simp only [aa17, Partial.Locals.set, ite_true]
  have empty16 : (p3.state.set 17 .empty) 16 = .empty := by
    simp only [Partial.Locals.set, show (16 : Nat) ≠ 17 by decide, ite_false]
    rw [ma17.prepare_closed_local _ 16 (by decide)]
    simp only [aa17, Partial.Locals.set, show (16 : Nat) ≠ 17 by decide, ite_false]
    rw [m17.prepare_closed_local _ 16 (by decide)]
    simp only [a17, Partial.Locals.set, show (16 : Nat) ≠ 17 by decide, ite_false]
    rw [m16.prepare_closed_local _ 16 (by decide)]
    simp only [a16, Partial.Locals.set, ite_true]
  have bound16p3 : p3.roots 16 = some root16 := by change p2.roots 16 = some root16; exact bound16p2
  have bound0p3 : p3.roots 0 = some root0 := by change p2.roots 0 = some root0; exact bound0p2
  obtain ⟨cell16, assign16, ma16⟩ := m3.assign_empty bound16p3 (by decide) raw16a17 (empty_result_source ready17) empty16
    (m3.closed.clear 17)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set])
    (by intro op member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> trivial)
    (result_typed emptyWitness) (.adt .embedding)
  let wa16 := wa17.write root16.address cell16
  let aa16 : Activation := {p3 with state := (p3.state.set 17 .empty).set 16 (Slot.ofValue (encodeResult emptyWitness))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa16 aa16 at ma16
  have ia16 : InputLocals left right table aa16.state := (i3.set 17 .empty (by decide)).set 16 _ (by decide)
  have raw0a16 := Activation.write_other_root m3.native.valid bound16p3 bound0p3 (by decide) raw0a17 cell16
  let p4 := aa16.forgetRefs (emptyCode 4)
  have m4 := ma16.prepare (emptyCode 4)
  have i4 := ia16.prepare_empty 4 (by decide)
  have empty17p4 : p4.state 17 = .empty := by
    rw [ma16.prepare_closed_local _ 17 (by decide)]
    simp only [aa16, Partial.Locals.set, show (17 : Nat) ≠ 16 by decide, ite_false, ite_true]
  have bound17p4 : p4.roots 17 = some root17 := by change p2.roots 17 = some root17; exact bound17
  obtain ⟨drop17, md17⟩ := m4.drop_zero bound17p4 (by rw [empty17p4]; simp only [Slot.dropWork])
  let ad17 : Activation := {p4 with state := p4.state.set 17 .empty}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa16 ad17 at md17
  have id17 : InputLocals left right table ad17.state := i4.set 17 .empty (by decide)
  let p5 := ad17.forgetRefs (emptyCode 5)
  have m5 := md17.prepare (emptyCode 5)
  have i5 := id17.prepare_empty 5 (by decide)
  have bound17p5 : p5.roots 17 = some root17 := by change p4.roots 17 = some root17; exact bound17p4
  obtain ⟨end17, me17⟩ := m5.storageDead bound17p5 (by
    rw [md17.prepare_closed_local _ 17 (by decide)]
    simp only [ad17, Partial.Locals.set, ite_true, Slot.dropWork])
  let final := wa16.retire [root17.address]
  let ae17 : Activation := {p5 with roots := p5.roots.set 17 none, state := p5.state.set 17 .empty}
  change OriginalLoanMachine before callers previous external [1, 2, 13] final ae17 at me17
  have ie17 : InputLocals left right table ae17.state := i5.set 17 .empty (by decide)
  let after := ae17.forgetRefs (emptyCode 6)
  have finalMachine := me17.prepare (emptyCode 6)
  have finalInputs := ie17.prepare_empty 6 (by decide)
  have whole : Calling.Prefix callee callers (emptyCode 7) (emptyActions.take 7) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 16) live16)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 17) live17)
        (.cons (Calling.instruction_noncall_run (act := .assign 17 (.aggregate .word 0 [])) assign17)
          (.cons (Calling.instruction_noncall_run (act := .assign 16 (.aggregate .embedding 0 [.move (.local 17), .number 0])) assign16)
            (.cons (Calling.instruction_noncall_run (act := .drop 17) drop17)
              (.cons (Calling.instruction_noncall_run (act := .storageDead 17) end17)
                (.cons (Calling.instruction_noncall_run (act := .fakeRead (.local 16)) rfl) (.nil _ _)))))))
  have tail : Calling.Prefix callee callers (emptyCode 7) ((emptyActions.drop 4).take 3) wa16 aa16 final after :=
    .cons (Calling.instruction_noncall_run (act := .drop 17) drop17)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 17) end17)
        (.cons (Calling.instruction_noncall_run (act := .fakeRead (.local 16)) rfl) (.nil _ _)))
  have value16 : aa16.state 16 = Slot.ofValue (encodeResult emptyWitness) := by simp only [aa16, Partial.Locals.set, ite_true]
  refine ⟨final, after, root16, whole, finalMachine, finalInputs, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, ae17, p5, ad17, p4, aa16, p3, aa17, p2, a17, p1, a16, Roots.set, Activation.forgetRefs]
  · simp [after, ae17, Roots.set, Activation.forgetRefs]
  · intro slot outside
    have sixteen : slot ≠ 16 := by intro same; subst slot; simp at outside
    have seventeen : slot ≠ 17 := by intro same; subst slot; simp at outside
    simp only [after, ae17, p5, ad17, p4, aa16, p3, aa17, p2, a17, p1, a16, p0,
      Activation.forgetRefs, Roots.set, sixteen, seventeen, ite_false]
  · exact (tail.closed_local_same (index := 16) ma16.native.valid ma16.native.callersValid ma16.native.wellFormed
      (by rw [value16]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value16
  · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  · exact (whole.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.returnEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.returnEmpty
  · refine ⟨root0, ?_, raw0a16⟩
    simpa [after, ae17, p5, ad17, p4, aa16, p3, aa17, p2, a17, p1, a16, p0, Roots.set, Activation.forgetRefs] using bound0

end SubtreeProofs.Rust.SourceEval.Evaluator
