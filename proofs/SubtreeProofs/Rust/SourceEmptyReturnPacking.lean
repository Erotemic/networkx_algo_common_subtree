module

public import SubtreeProofs.Rust.SourceEmptyInsertRetirement

/-! Construct the nine actual result-packing instructions: move the witness
through the optional-result temporary, retire it, move the inserted table, and
assemble the native output tuple in the original fresh return slot. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_return_packing_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    (result : CommonEmbedding) (table : MemoTable)
    (witness : active.state 16 = Slot.ofValue (encodeResult result)) (tableValue : active.state 18 = Slot.ofValue (encodeTable table))
    {root0 : Binding} (bound0 : active.roots 0 = some root0) (raw0 : world.memory[root0.address]? = some (.node .tuple 0 []))
    (empty0 : active.state 0 = .empty) (count : 27 ≤ active.count)
    (unbound : ∀ slot ∈ [24, 25, 26], active.roots slot = none) :
    ∃ (final : World) (after : Activation) (root24 root26 : Binding),
      Calling.Prefix callee callers (emptyCode 34) ((emptyActions.drop 25).take 9) world active final after ∧
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧ after.count = active.count ∧
      after.roots 24 = some root24 ∧ after.roots 25 = none ∧ after.roots 26 = some root26 ∧
      (∀ slot, slot ∉ [24, 25, 26] → after.roots slot = active.roots slot) ∧
      after.state 0 = Slot.ofValue (encodeOutput (some result) table) ∧ after.state 16 = .empty ∧
      after.state 18 = .empty ∧ after.state 24 = .empty ∧ after.state 26 = .empty := by
  let p25 := active.forgetRefs (emptyCode 25)
  have m25 := h.prepare (emptyCode 25)
  let root24 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w24 := world.allocate (.stack p25.frame 24 world.memory.length) (.node .tuple 0 [])
  let a24 : Activation := {p25 with roots := p25.roots.set 24 (some root24), state := p25.state.set 24 .empty}
  obtain ⟨live24, m24⟩ := m25.storageLive (slot := 24) (by change 24 < active.count; omega) (unbound 24 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w24 a24 at m24
  let p26 := a24.forgetRefs (emptyCode 26)
  have m26 := m24.prepare (emptyCode 26)
  let root25 : Binding := ⟨w24.memory.length, w24.memory.length⟩
  let w25 := w24.allocate (.stack p26.frame 25 w24.memory.length) (.node .tuple 0 [])
  let a25 : Activation := {p26 with roots := p26.roots.set 25 (some root25), state := p26.state.set 25 .empty}
  obtain ⟨live25, m27⟩ := m26.storageLive (slot := 25) (by change 25 < active.count; omega)
    (by simpa [p26, a24, p25, Roots.set, Activation.forgetRefs] using unbound 25 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w25 a25 at m27
  let p27 := a25.forgetRefs (emptyCode 27)
  have m27p := m27.prepare (emptyCode 27)
  have bound25 : p27.roots 25 = some root25 := by simp [p27, a25, Roots.set, Activation.forgetRefs]
  have bound24p27 : p27.roots 24 = some root24 := by simp [p27, a25, p26, a24, Roots.set, Activation.forgetRefs]
  have bound0p27 : p27.roots 0 = some root0 := by simpa [p27, a25, p26, a24, p25, Roots.set, Activation.forgetRefs] using bound0
  have sourceWitness : p27.state 16 = Slot.ofValue (encodeResult result) := by
    have before : Calling.Prefix callee callers (emptyCode 27) [.storageLive 24, .storageLive 25] world active w25 a25 :=
      .cons (Calling.instruction_noncall_run (act := .storageLive 24) live24)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 25) live25) (.nil _ _))
    exact (m27.prepare_closed_local _ 16 (by decide)).trans
      ((before.closed_local_same (index := 16) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [witness]; exact ofValue_typed (result_typed result)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans witness)
  have empty25 : (p27.state.set 16 .empty) 25 = .empty := by
    simp only [Partial.Locals.set, show (25 : Nat) ≠ 16 by decide, ite_false]
    rw [m27.prepare_closed_local _ 25 (by decide)]
    simp only [a25, Partial.Locals.set, ite_true]
  obtain ⟨cell25, assign25, ma25⟩ := m27p.assign_empty bound25 (by decide) (w24.allocate_spec _ _).2.1
    (use_local_source (state := p27.state) (slot := 16) (by rw [sourceWitness]; exact Slot.materialize_ofValue _)) empty25 (m27p.closed.clear 16)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set, p27]) trivial (result_typed result) (.adt .embedding)
  let wa25 := w25.write root25.address cell25
  let aa25 : Activation := {p27 with state := (p27.state.set 16 .empty).set 25 (Slot.ofValue (encodeResult result))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa25 aa25 at ma25
  have raw0w24 : w24.memory[root0.address]? = some (.node .tuple 0 []) := (world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ raw0
  have raw0w25 : w25.memory[root0.address]? = some (.node .tuple 0 []) := (w24.allocate_keeps m24.native.wellFormed _ _ []).memory _ _ raw0w24
  have raw0a25 := Activation.write_other_root m27p.native.valid bound25 bound0p27 (by decide) raw0w25 cell25
  have raw24w25 : w25.memory[root24.address]? = some (.node .tuple 0 []) :=
    (w24.allocate_keeps m24.native.wellFormed _ _ []).memory _ _ (world.allocate_spec _ _).2.1
  have raw24a25 := Activation.write_other_root m27p.native.valid bound25 bound24p27 (by decide) raw24w25 cell25
  let p28 := aa25.forgetRefs (emptyCode 28)
  have m28 := ma25.prepare (emptyCode 28)
  have ready25 : p28.state 25 = Slot.ofValue (encodeResult result) := by
    rw [ma25.prepare_closed_local _ 25 (by decide)]
    simp only [aa25, Partial.Locals.set, ite_true]
  have empty24 : (p28.state.set 25 .empty) 24 = .empty := by
    simp only [Partial.Locals.set, show (24 : Nat) ≠ 25 by decide, ite_false]
    rw [ma25.prepare_closed_local _ 24 (by decide)]
    simp only [aa25, Partial.Locals.set, show (24 : Nat) ≠ 25 by decide, show (24 : Nat) ≠ 16 by decide, ite_false]
    rw [m27.prepare_closed_local _ 24 (by decide)]
    simp only [a25, Partial.Locals.set, show (24 : Nat) ≠ 25 by decide, ite_false]
    rw [m24.prepare_closed_local _ 24 (by decide)]
    simp only [a24, Partial.Locals.set, ite_true]
  have bound24p28 : p28.roots 24 = some root24 := by change p27.roots 24 = some root24; exact bound24p27
  have bound0p28 : p28.roots 0 = some root0 := by change p27.roots 0 = some root0; exact bound0p27
  obtain ⟨cell24, assign24, ma24⟩ := m28.assign_empty bound24p28 (by decide) raw24a25
    (aggregate_one_source (state := p28.state) (slot := 25) (by rw [ready25]; exact Slot.materialize_ofValue _) .optional 1)
    empty24 (m28.closed.clear 25)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set, p28])
    (by intro op member; have same := List.mem_singleton.mp member; subst op; trivial) (option_typed (some result)) (.adt .optional)
  let wa24 := wa25.write root24.address cell24
  let aa24 : Activation := {p28 with state := (p28.state.set 25 .empty).set 24 (Slot.ofValue (encodeOption (some result)))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa24 aa24 at ma24
  have raw0a24 := Activation.write_other_root m28.native.valid bound24p28 bound0p28 (by decide) raw0a25 cell24
  let p29 := aa24.forgetRefs (emptyCode 29)
  have m29 := ma24.prepare (emptyCode 29)
  have bound25p29 : p29.roots 25 = some root25 := by change p27.roots 25 = some root25; exact bound25
  have zero25 : p29.state 25 = .empty := by
    rw [ma24.prepare_closed_local _ 25 (by decide)]
    simp only [aa24, Partial.Locals.set, show (25 : Nat) ≠ 24 by decide, ite_false, ite_true]
  obtain ⟨drop25, md25⟩ := m29.drop_zero bound25p29 (by rw [zero25]; simp only [Slot.dropWork])
  let ad25 : Activation := {p29 with state := p29.state.set 25 .empty}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa24 ad25 at md25
  let p30 := ad25.forgetRefs (emptyCode 30)
  have m30 := md25.prepare (emptyCode 30)
  have bound25p30 : p30.roots 25 = some root25 := by change p29.roots 25 = some root25; exact bound25p29
  obtain ⟨end25, me25⟩ := m30.storageDead bound25p30 (by
    rw [md25.prepare_closed_local _ 25 (by decide)]
    simp only [ad25, Partial.Locals.set, ite_true, Slot.dropWork])
  let we25 := wa24.retire [root25.address]
  let ae25 : Activation := {p30 with roots := p30.roots.set 25 none, state := p30.state.set 25 .empty}
  change OriginalLoanMachine before callers previous external [1, 2, 13] we25 ae25 at me25
  let p31 := ae25.forgetRefs (emptyCode 31)
  have m31 := me25.prepare (emptyCode 31)
  let root26 : Binding := ⟨we25.memory.length, we25.memory.length⟩
  let w26 := we25.allocate (.stack p31.frame 26 we25.memory.length) (.node .tuple 0 [])
  let a26 : Activation := {p31 with roots := p31.roots.set 26 (some root26), state := p31.state.set 26 .empty}
  obtain ⟨live26, m26⟩ := m31.storageLive (slot := 26) (by change 26 < active.count; omega)
    (by simpa [p31, ae25, p30, ad25, p29, aa24, p28, aa25, p27, a25, p26, a24, p25, Roots.set, Activation.forgetRefs] using unbound 26 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [1, 2, 13] w26 a26 at m26
  have seven : Calling.Prefix callee callers (emptyCode 32) ((emptyActions.drop 25).take 7) world active w26 a26 :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 24) live24)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 25) live25)
        (.cons (Calling.instruction_noncall_run (act := .assign 25 (.use (.move (.local 16)))) assign25)
          (.cons (Calling.instruction_noncall_run (act := .assign 24 (.aggregate .optional 1 [.move (.local 25)])) assign24)
            (.cons (Calling.instruction_noncall_run (act := .drop 25) drop25)
              (.cons (Calling.instruction_noncall_run (act := .storageDead 25) end25)
                (.cons (Calling.instruction_noncall_run (act := .storageLive 26) live26) (.nil _ _)))))))
  let p32 := a26.forgetRefs (emptyCode 32)
  have m32 := m26.prepare (emptyCode 32)
  have bound26 : p32.roots 26 = some root26 := by simp [p32, a26, Roots.set, Activation.forgetRefs]
  have bound0p32 : p32.roots 0 = some root0 := by
    simpa [p32, a26, p31, ae25, p30, ad25, p29, aa24, p28, aa25, p27, a25, p26, a24, p25, Roots.set, Activation.forgetRefs] using bound0
  have ready18 : p32.state 18 = Slot.ofValue (encodeTable table) :=
    (m26.prepare_closed_local _ 18 (by decide)).trans
      ((seven.closed_local_same (index := 18) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans tableValue)
  have empty26 : (p32.state.set 18 .empty) 26 = .empty := by
    simp only [Partial.Locals.set, show (26 : Nat) ≠ 18 by decide, ite_false]
    rw [m26.prepare_closed_local _ 26 (by decide)]
    simp only [a26, Partial.Locals.set, ite_true]
  obtain ⟨cell26, assign26, ma26⟩ := m32.assign_empty bound26 (by decide) (we25.allocate_spec _ _).2.1
    (use_local_source (state := p32.state) (slot := 18) (by rw [ready18]; exact Slot.materialize_ofValue _)) empty26 (m32.closed.clear 18)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set, p32]) trivial (table_typed table) (.adt .table)
  let wa26 := w26.write root26.address cell26
  let aa26 : Activation := {p32 with state := (p32.state.set 18 .empty).set 26 (Slot.ofValue (encodeTable table))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] wa26 aa26 at ma26
  have raw0w26 : w26.memory[root0.address]? = some (.node .tuple 0 []) :=
    (we25.allocate_keeps me25.native.wellFormed _ _ []).memory _ _ raw0a24
  have raw0a26 := Activation.write_other_root m32.native.valid bound26 bound0p32 (by decide) raw0w26 cell26
  have option24 : aa24.state 24 = Slot.ofValue (encodeOption (some result)) := by simp only [aa24, Partial.Locals.set, ite_true]
  have rest24 : Calling.Prefix callee callers (emptyCode 33) ((emptyActions.drop 29).take 4) wa24 aa24 wa26 aa26 :=
    .cons (Calling.instruction_noncall_run (act := .drop 25) drop25)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 25) end25)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 26) live26)
          (.cons (Calling.instruction_noncall_run (act := .assign 26 (.use (.move (.local 18)))) assign26) (.nil _ _))))
  let p33 := aa26.forgetRefs (emptyCode 33)
  have m33 := ma26.prepare (emptyCode 33)
  have ready24 : p33.state 24 = Slot.ofValue (encodeOption (some result)) :=
    (ma26.prepare_closed_local _ 24 (by decide)).trans
      ((rest24.closed_local_same (index := 24) ma24.native.valid ma24.native.callersValid ma24.native.wellFormed
        (by rw [option24]; exact ofValue_typed (option_typed (some result))) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans option24)
  have ready26 : p33.state 26 = Slot.ofValue (encodeTable table) := by
    rw [ma26.prepare_closed_local _ 26 (by decide)]
    simp only [aa26, Partial.Locals.set, ite_true]
  have bound0p33 : p33.roots 0 = some root0 := by change p32.roots 0 = some root0; exact bound0p32
  have eight : Calling.Prefix callee callers (emptyCode 33) ((emptyActions.drop 25).take 8) world active wa26 aa26 :=
    Calling.Prefix.append (suffix := emptyCode 33) (rest := [.assign 26 (.use (.move (.local 18)))]) seven
      (.cons (Calling.instruction_noncall_run (act := .assign 26 (.use (.move (.local 18)))) assign26) (.nil _ _))
  have emptyReturn : ((p33.state.set 24 .empty).set 26 .empty) 0 = .empty := by
    simp only [Partial.Locals.set, show (0 : Nat) ≠ 26 by decide, show (0 : Nat) ≠ 24 by decide, ite_false]
    rw [ma26.prepare_closed_local _ 0 (by decide)]
    exact (eight.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty0]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty0
  obtain ⟨cell0, assign0, finalMachine⟩ := m33.assign_empty bound0p33 (by decide) raw0a26
    (aggregate_two_source (state := p33.state) (first := 24) (second := 26)
      (by rw [ready24]; exact Slot.materialize_ofValue _) (by rw [ready26]; exact Slot.materialize_ofValue _) (by decide) .tuple 0)
    emptyReturn ((m33.closed.clear 24).clear 26)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl <;> simp [Partial.Locals.set, p33])
    (by intro op member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> trivial)
    (encodeOutput_typed (some result) table) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
  let final := wa26.write root0.address cell0
  let after : Activation := {p33 with state := ((p33.state.set 24 .empty).set 26 .empty).set 0 (Slot.ofValue (encodeOutput (some result) table))}
  change OriginalLoanMachine before callers previous external [1, 2, 13] final after at finalMachine
  have whole : Calling.Prefix callee callers (emptyCode 34) ((emptyActions.drop 25).take 9) world active final after :=
    Calling.Prefix.append (suffix := emptyCode 34) (rest := [.assign 0 (.aggregate .tuple 0 [.move (.local 24), .move (.local 26)])]) eight
      (.cons (Calling.instruction_noncall_run (act := .assign 0 (.aggregate .tuple 0 [.move (.local 24), .move (.local 26)])) assign0) (.nil _ _))
  have empty16AtA25 : aa25.state 16 = .empty := by simp only [aa25, Partial.Locals.set, show (16 : Nat) ≠ 25 by decide, ite_false, ite_true]
  have tail16 : Calling.Prefix callee callers (emptyCode 34) ((emptyActions.drop 28).take 6) wa25 aa25 final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 24 (.aggregate .optional 1 [.move (.local 25)])) assign24)
      (.cons (Calling.instruction_noncall_run (act := .drop 25) drop25)
        (.cons (Calling.instruction_noncall_run (act := .storageDead 25) end25)
          (.cons (Calling.instruction_noncall_run (act := .storageLive 26) live26)
            (.cons (Calling.instruction_noncall_run (act := .assign 26 (.use (.move (.local 18)))) assign26)
              (.cons (Calling.instruction_noncall_run (act := .assign 0 (.aggregate .tuple 0 [.move (.local 24), .move (.local 26)])) assign0) (.nil _ _))))))
  refine ⟨final, after, root24, root26, whole, finalMachine, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [after, p33, aa26, p32, a26, p31, ae25, p30, ad25, p29, aa24, p28, aa25, p27, a25, p26, a24, Roots.set, Activation.forgetRefs]
  · simp [after, p33, aa26, p32, a26, p31, ae25, Roots.set, Activation.forgetRefs]
  · simp [after, p33, aa26, p32, a26, Roots.set, Activation.forgetRefs]
  · intro slot outside
    have twentyFour : slot ≠ 24 := by intro same; subst slot; simp at outside
    have twentyFive : slot ≠ 25 := by intro same; subst slot; simp at outside
    have twentySix : slot ≠ 26 := by intro same; subst slot; simp at outside
    simp only [after, p33, aa26, p32, a26, p31, ae25, p30, ad25, p29, aa24, p28, aa25, p27, a25, p26, a24, p25,
      Activation.forgetRefs, Roots.set, twentyFour, twentyFive, twentySix, ite_false]
  · simp only [after, Partial.Locals.set, ite_true]
  · exact (tail16.closed_local_same (index := 16) ma25.native.valid ma25.native.callersValid ma25.native.wellFormed
      (by rw [empty16AtA25]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty16AtA25
  · simp only [after, Partial.Locals.set, show (18 : Nat) ≠ 0 by decide, show (18 : Nat) ≠ 26 by decide, show (18 : Nat) ≠ 24 by decide, ite_false]
    rw [ma26.prepare_closed_local _ 18 (by decide)]
    simp only [aa26, Partial.Locals.set, show (18 : Nat) ≠ 26 by decide, ite_false, ite_true]
  · simp [after, Partial.Locals.set]

end SubtreeProofs.Rust.SourceEval.Evaluator
