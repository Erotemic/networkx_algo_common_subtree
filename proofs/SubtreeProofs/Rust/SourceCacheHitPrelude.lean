module

public import SubtreeProofs.Rust.SourceCacheHitScope

/-! Construct the first nine real cache-hit instructions: extract the copied
lookup payload, wrap it in the return option, retire its temporary view and open
table-transfer storage. Original query/table aliases remain allowed. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem hit_prelude_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 13 ≤ active.count)
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result) :
    ∃ (final : World) (after : Activation) (root9 root10 root12 : Binding),
      Calling.Prefix callee callers (hitCode 9) (hitActions.take 9) world active final after ∧
      QueryMachine before callers previous external final after ∧ after.count = active.count ∧
      (∀ slot, slot ∉ [9, 10, 11, 12] → after.roots slot = active.roots slot) ∧
      after.roots 9 = some root9 ∧ after.roots 10 = some root10 ∧ after.roots 11 = none ∧ after.roots 12 = some root12 ∧
      final.memory[root12.address]? = some (.node .tuple 0 []) ∧
      (∃ root0, after.roots 0 = some root0 ∧ final.memory[root0.address]? = some (.node .tuple 0 [])) ∧
      after.state 0 = .empty ∧ after.state 3 = Slot.ofValue (encodeTable table) ∧
      after.state 4 = .node .optional 1 [.empty] ∧ after.state 6 = .empty ∧ after.state 9 = .empty ∧
      after.state 10 = Slot.ofValue (encodeOption (some result)) ∧ after.state 12 = .empty := by
  obtain ⟨root0, root0Binding, root0Memory⟩ := scope.returnRoot
  let p0 := active.forgetRefs (hitCode 0)
  have m0 := h.prepare (hitCode 0)
  let root9 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w9 := world.allocate (.stack p0.frame 9 world.memory.length) (.node .tuple 0 [])
  let a9 : Activation := {p0 with roots := p0.roots.set 9 (some root9), state := p0.state.set 9 .empty}
  obtain ⟨live9, m9⟩ := m0.storageLive (slot := 9) (by change 9 < active.count; omega)
    (scope.unbound_hit_local unbound (by simp)) (by decide)
  change QueryMachine before callers previous external w9 a9 at m9
  let p1 := a9.forgetRefs (hitCode 1)
  have m1 := m9.prepare (hitCode 1)
  have ready4 : p1.state 4 = Slot.ofValue (encodeOption (some result)) := by
    calc
      p1.state 4 = a9.state 4 := m9.prepare_closed_local _ _ (by decide)
      _ = p0.state 4 := by simp only [a9, Partial.Locals.set, show (4 : Nat) ≠ 9 by decide, ite_false]
      _ = active.state 4 := h.prepare_closed_local _ _ (by decide)
      _ = _ := scope.hit_value hit
  have root9Binding : p1.roots 9 = some root9 := by simp [p1, a9, Roots.set, Activation.forgetRefs]
  have root0p1 : p1.roots 0 = some root0 := by
    simpa [p1, a9, p0, Activation.forgetRefs, Roots.set] using root0Binding
  have empty9 : (p1.state.set 4 (.node .optional 1 [.empty])) 9 = .empty := by
    simp only [Partial.Locals.set, show (9 : Nat) ≠ 4 by decide, ite_false]
    rw [m9.prepare_closed_local _ 9 (by decide)]
    simp only [a9, Partial.Locals.set, ite_true]
  obtain ⟨cell9, assign9, mr9⟩ := m1.assign_empty root9Binding (by decide) (world.allocate_spec _ _).2.1
    (move_cached_payload_source result ready4) empty9
    (m1.closed.set 4 cached_payload_hole_typed (.adt .optional))
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set]) trivial (result_typed result) (.adt .embedding)
  let wr9 := w9.write root9.address cell9
  let ar9 : Activation := {p1 with state := (p1.state.set 4 (.node .optional 1 [.empty])).set 9 (Slot.ofValue (encodeResult result))}
  change QueryMachine before callers previous external wr9 ar9 at mr9
  have read0w9 : w9.memory[root0.address]? = some (.node .tuple 0 []) :=
    (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ root0Memory
  have read0r9 := Activation.write_other_root m1.native.valid root9Binding root0p1 (by decide) read0w9 cell9
  let p2 := ar9.forgetRefs (hitCode 2)
  have m2 := mr9.prepare (hitCode 2)
  let root10 : Binding := ⟨wr9.memory.length, wr9.memory.length⟩
  let w10 := wr9.allocate (.stack p2.frame 10 wr9.memory.length) (.node .tuple 0 [])
  let a10 : Activation := {p2 with roots := p2.roots.set 10 (some root10), state := p2.state.set 10 .empty}
  obtain ⟨live10, m10⟩ := m2.storageLive (slot := 10) (by change 10 < active.count; omega)
    (by simpa [p2, ar9, p1, a9, p0, Activation.forgetRefs, Roots.set] using scope.unbound_hit_local unbound (slot := 10) (by simp)) (by decide)
  change QueryMachine before callers previous external w10 a10 at m10
  let p3 := a10.forgetRefs (hitCode 3)
  have m3 := m10.prepare (hitCode 3)
  let root11 : Binding := ⟨w10.memory.length, w10.memory.length⟩
  let w11 := w10.allocate (.stack p3.frame 11 w10.memory.length) (.node .tuple 0 [])
  let a11 : Activation := {p3 with roots := p3.roots.set 11 (some root11), state := p3.state.set 11 .empty}
  obtain ⟨live11, m11⟩ := m3.storageLive (slot := 11) (by change 11 < active.count; omega)
    (by simpa [p3, a10, p2, ar9, p1, a9, p0, Activation.forgetRefs, Roots.set] using scope.unbound_hit_local unbound (slot := 11) (by simp)) (by decide)
  change QueryMachine before callers previous external w11 a11 at m11
  let p4 := a11.forgetRefs (hitCode 4)
  have m4 := m11.prepare (hitCode 4)
  have root11Binding : p4.roots 11 = some root11 := by simp [p4, a11, Roots.set, Activation.forgetRefs]
  have root10p4 : p4.roots 10 = some root10 := by simp [p4, a11, p3, a10, Roots.set, Activation.forgetRefs]
  have root0p4 : p4.roots 0 = some root0 := by
    simpa [p4, a11, p3, a10, p2, ar9, p1, a9, p0, Activation.forgetRefs, Roots.set] using root0Binding
  have ready9 : p4.state 9 = Slot.ofValue (encodeResult result) := by
    have steps : Calling.Prefix callee callers (hitCode 4) [.storageLive 10, .storageLive 11] wr9 ar9 w11 a11 :=
      .cons (Calling.instruction_noncall_run (act := .storageLive 10) live10)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 11) live11) (.nil _ _))
    have value9 : ar9.state 9 = Slot.ofValue (encodeResult result) := by simp only [ar9, Partial.Locals.set, ite_true]
    have stable := steps.closed_local_same (index := 9) mr9.native.valid mr9.native.callersValid mr9.native.wellFormed
      (by rw [value9]; exact ofValue_typed (result_typed result)) (.adt .embedding) (by decide +kernel) (by decide +kernel)
    exact (m11.prepare_closed_local _ 9 (by decide)).trans (stable.trans value9)
  have empty11 : (p4.state.set 9 .empty) 11 = .empty := by
    simp only [Partial.Locals.set, show (11 : Nat) ≠ 9 by decide, ite_false]
    rw [m11.prepare_closed_local _ 11 (by decide)]
    simp only [a11, Partial.Locals.set, ite_true]
  obtain ⟨cell11, assign11, mr11⟩ := m4.assign_empty root11Binding (by decide) (w10.allocate_spec _ _).2.1
    (use_local_source (by rw [ready9]; exact Slot.materialize_ofValue _)) empty11 (m4.closed.clear 9)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set]) trivial (result_typed result) (.adt .embedding)
  let wr11 := w11.write root11.address cell11
  let ar11 : Activation := {p4 with state := (p4.state.set 9 .empty).set 11 (Slot.ofValue (encodeResult result))}
  change QueryMachine before callers previous external wr11 ar11 at mr11
  have read0w10 : w10.memory[root0.address]? = some (.node .tuple 0 []) :=
    (wr9.allocate_keeps mr9.native.wellFormed _ _ []).memory _ _ read0r9
  have read0w11 : w11.memory[root0.address]? = some (.node .tuple 0 []) :=
    (w10.allocate_keeps m10.native.wellFormed _ _ []).memory _ _ read0w10
  have read0r11 := Activation.write_other_root m4.native.valid root11Binding root0p4 (by decide) read0w11 cell11
  have read10w11 : w11.memory[root10.address]? = some (.node .tuple 0 []) :=
    (w10.allocate_keeps m10.native.wellFormed _ _ []).memory _ _ (wr9.allocate_spec _ _).2.1
  have read10r11 := Activation.write_other_root m4.native.valid root11Binding root10p4 (by decide) read10w11 cell11
  let p5 := ar11.forgetRefs (hitCode 5)
  have m5 := mr11.prepare (hitCode 5)
  have ready11 : p5.state 11 = Slot.ofValue (encodeResult result) := by
    rw [mr11.prepare_closed_local _ 11 (by decide)]
    simp only [ar11, Partial.Locals.set, ite_true]
  have empty10 : (p5.state.set 11 .empty) 10 = .empty := by
    simp only [Partial.Locals.set, show (10 : Nat) ≠ 11 by decide, ite_false]
    rw [mr11.prepare_closed_local _ 10 (by decide)]
    simp only [ar11, Partial.Locals.set, show (10 : Nat) ≠ 11 by decide, show (10 : Nat) ≠ 9 by decide, ite_false]
    rw [m11.prepare_closed_local _ 10 (by decide)]
    simp only [a11, Partial.Locals.set, show (10 : Nat) ≠ 11 by decide, ite_false]
    rw [m10.prepare_closed_local _ 10 (by decide)]
    simp only [a10, Partial.Locals.set, ite_true]
  have root10Binding : p5.roots 10 = some root10 := root10p4
  have root0p5 : p5.roots 0 = some root0 := root0p4
  obtain ⟨cell10, assign10, mr10⟩ := m5.assign_empty root10Binding (by decide) read10r11
    (aggregate_one_source (by rw [ready11]; exact Slot.materialize_ofValue _) .optional 1) empty10 (m5.closed.clear 11)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set])
    (by intro op member; have same : op = .move (.local 11) := List.mem_singleton.mp member; subst op; trivial)
    (option_typed (some result)) (.adt .optional)
  let wr10 := wr11.write root10.address cell10
  let ar10 : Activation := {p5 with state := (p5.state.set 11 .empty).set 10 (Slot.ofValue (encodeOption (some result)))}
  change QueryMachine before callers previous external wr10 ar10 at mr10
  have read0r10 := Activation.write_other_root m5.native.valid root10Binding root0p5 (by decide) read0r11 cell10
  let p6 := ar10.forgetRefs (hitCode 6)
  have m6 := mr10.prepare (hitCode 6)
  have root11p6 : p6.roots 11 = some root11 := root11Binding
  have empty11p6 : p6.state 11 = .empty := by
    rw [mr10.prepare_closed_local _ 11 (by decide)]
    simp only [ar10, Partial.Locals.set, show (11 : Nat) ≠ 10 by decide, ite_false, ite_true]
  obtain ⟨drop11, md11⟩ := m6.drop_zero root11p6 (by rw [empty11p6]; simp only [Slot.dropWork])
  let ad11 : Activation := {p6 with state := p6.state.set 11 .empty}
  change QueryMachine before callers previous external wr10 ad11 at md11
  let p7 := ad11.forgetRefs (hitCode 7)
  have m7 := md11.prepare (hitCode 7)
  have root11p7 : p7.roots 11 = some root11 := root11p6
  obtain ⟨end11, me11⟩ := m7.storageDead root11p7 (by
    rw [md11.prepare_closed_local _ 11 (by decide)]
    simp only [ad11, Partial.Locals.set, ite_true, Slot.dropWork])
  let we11 := wr10.retire [root11.address]
  let ae11 : Activation := {p7 with roots := p7.roots.set 11 none, state := p7.state.set 11 .empty}
  change QueryMachine before callers previous external we11 ae11 at me11
  let p8 := ae11.forgetRefs (hitCode 8)
  have m8 := me11.prepare (hitCode 8)
  let root12 : Binding := ⟨we11.memory.length, we11.memory.length⟩
  let final := we11.allocate (.stack p8.frame 12 we11.memory.length) (.node .tuple 0 [])
  let after : Activation := {p8 with roots := p8.roots.set 12 (some root12), state := p8.state.set 12 .empty}
  obtain ⟨live12, m12⟩ := m8.storageLive (slot := 12) (by change 12 < active.count; omega)
    (by simpa [p8, ae11, p7, ad11, p6, ar10, p5, ar11, p4, a11, p3, a10, p2, ar9, p1, a9, p0,
      Activation.forgetRefs, Roots.set] using scope.unbound_hit_local unbound (slot := 12) (by simp)) (by decide)
  change QueryMachine before callers previous external final after at m12
  have whole : Calling.Prefix callee callers (hitCode 9) (hitActions.take 9) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 9) live9)
      (.cons (Calling.instruction_noncall_run (act := .assign 9 (.use (.move (.field (.local 4) (some 1) 0)))) assign9)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 10) live10)
          (.cons (Calling.instruction_noncall_run (act := .storageLive 11) live11)
            (.cons (Calling.instruction_noncall_run (act := .assign 11 (.use (.move (.local 9)))) assign11)
              (.cons (Calling.instruction_noncall_run (act := .assign 10 (.aggregate .optional 1 [.move (.local 11)])) assign10)
                (.cons (Calling.instruction_noncall_run (act := .drop 11) drop11)
                  (.cons (Calling.instruction_noncall_run (act := .storageDead 11) end11)
                    (.cons (Calling.instruction_noncall_run (act := .storageLive 12) live12) (.nil _ _)))))))))
  have part4 : ar9.state 4 = .node .optional 1 [.empty] := by simp [ar9, Partial.Locals.set]
  have part9 : ar11.state 9 = .empty := by simp [ar11, Partial.Locals.set]
  have part10 : ar10.state 10 = Slot.ofValue (encodeOption (some result)) := by simp only [ar10, Partial.Locals.set, ite_true]
  have tail4 : Calling.Prefix callee callers (hitCode 9) ((hitActions.drop 2).take 7) wr9 ar9 final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 10) live10)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 11) live11)
        (.cons (Calling.instruction_noncall_run (act := .assign 11 (.use (.move (.local 9)))) assign11)
          (.cons (Calling.instruction_noncall_run (act := .assign 10 (.aggregate .optional 1 [.move (.local 11)])) assign10)
            (.cons (Calling.instruction_noncall_run (act := .drop 11) drop11)
              (.cons (Calling.instruction_noncall_run (act := .storageDead 11) end11)
                (.cons (Calling.instruction_noncall_run (act := .storageLive 12) live12) (.nil _ _)))))))
  have tail9 : Calling.Prefix callee callers (hitCode 9) ((hitActions.drop 5).take 4) wr11 ar11 final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 10 (.aggregate .optional 1 [.move (.local 11)])) assign10)
      (.cons (Calling.instruction_noncall_run (act := .drop 11) drop11)
        (.cons (Calling.instruction_noncall_run (act := .storageDead 11) end11)
          (.cons (Calling.instruction_noncall_run (act := .storageLive 12) live12) (.nil _ _))))
  have tail10 : Calling.Prefix callee callers (hitCode 9) ((hitActions.drop 6).take 3) wr10 ar10 final after :=
    .cons (Calling.instruction_noncall_run (act := .drop 11) drop11)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 11) end11)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 12) live12) (.nil _ _)))
  refine ⟨final, after, root9, root10, root12, whole, m12, rfl, ?_, ?_, ?_, ?_, ?_, (we11.allocate_spec _ _).2.1,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot member
    have nine : slot ≠ 9 := by intro same; subst slot; simp at member
    have ten : slot ≠ 10 := by intro same; subst slot; simp at member
    have eleven : slot ≠ 11 := by intro same; subst slot; simp at member
    have twelve : slot ≠ 12 := by intro same; subst slot; simp at member
    simp only [after, p8, ae11, p7, ad11, p6, ar10, p5, ar11, p4, a11, p3, a10, p2, ar9, p1, a9, p0,
      Activation.forgetRefs, Roots.set, nine, ten, eleven, twelve, ite_false]
  · simp [after, p8, ae11, p7, ad11, p6, ar10, p5, ar11, p4, a11, p3, a10, p2, ar9, p1, a9, Roots.set, Activation.forgetRefs]
  · simp [after, p8, ae11, p7, ad11, p6, ar10, p5, ar11, p4, a11, p3, a10, Roots.set, Activation.forgetRefs]
  · simp [after, p8, ae11, Roots.set, Activation.forgetRefs]
  · simp [after, Roots.set]
  · refine ⟨root0, ?_, (we11.allocate_keeps me11.native.wellFormed _ _ []).memory _ _ read0r10⟩
    simpa [after, p8, ae11, p7, ad11, p6, ar10, p5, ar11, p4, a11, p3, a10, p2, ar9, p1, a9, p0,
      Activation.forgetRefs, Roots.set] using root0Binding
  · have stable := whole.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.returnEmpty]; exact SlotTyped.empty .u32) .u32 (by decide +kernel) (by decide +kernel)
    exact stable.trans scope.returnEmpty
  · have stable := whole.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.inputs.table]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)
    exact stable.trans scope.inputs.table
  · have stable := tail4.closed_local_same (index := 4) mr9.native.valid mr9.native.callersValid mr9.native.wellFormed
      (by rw [part4]; exact cached_payload_hole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)
    exact stable.trans part4
  · have stable := whole.closed_local_same (index := 6) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.viewEnded]; exact SlotTyped.empty .u32) .u32 (by decide +kernel) (by decide +kernel)
    exact stable.trans scope.viewEnded
  · have stable := tail9.closed_local_same (index := 9) mr11.native.valid mr11.native.callersValid mr11.native.wellFormed
      (by rw [part9]; exact SlotTyped.empty .u32) .u32 (by decide +kernel) (by decide +kernel)
    exact stable.trans part9
  · have stable := tail10.closed_local_same (index := 10) mr10.native.valid mr10.native.callersValid mr10.native.wellFormed
      (by rw [part10]; exact ofValue_typed (option_typed (some result))) (.adt .optional) (by decide +kernel) (by decide +kernel)
    exact stable.trans part10
  · simp only [after, Partial.Locals.set, ite_true]

end SubtreeProofs.Rust.SourceEval.Evaluator
