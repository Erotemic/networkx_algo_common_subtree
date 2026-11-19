module

public import SubtreeProofs.Rust.SourceEvaluatorBorrowProgram

/-! Construct the actual evaluator's first four storage instructions with its
real continuation and reference preparation. The fresh roots, untouched native
inputs and complete ownership resources feed the following table/query borrows. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem storage_prefix_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    (count : 9 ≤ active.count) (left right : BalancedWord) (table : MemoTable)
    (inputs : InputLocals left right table active.state)
    (unbound : ∀ slot ∈ [0, 4, 5, 6, 7, 8], active.roots slot = none) :
    ∃ (final : World) (after : Activation) (returnRoot resultRoot firstView secondView : Binding),
      Calling.Prefix callee callers (borrowCode 4) (borrowPrefix.take 4) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.count = active.count ∧ after.roots 0 = some returnRoot ∧ after.roots 4 = some resultRoot ∧
      after.roots 5 = some firstView ∧ after.roots 6 = some secondView ∧
      final.memory[resultRoot.address]? = some (.node .tuple 0 []) ∧
      final.memory[firstView.address]? = some (.node .tuple 0 []) ∧
      final.memory[secondView.address]? = some (.node .tuple 0 []) ∧
      after.state 4 = .empty ∧ after.state 5 = .empty ∧ after.state 6 = .empty ∧
      after.roots 7 = none ∧ after.roots 8 = none ∧
      final.memory[returnRoot.address]? = some (.node .tuple 0 []) ∧
      (∀ index, index ∉ [0, 4, 5, 6] → after.roots index = active.roots index) ∧ after.state 0 = .empty ∧
      (QueryOrigins world active before.memory.length → QueryOrigins final after before.memory.length) := by
  let p0 := active.forgetRefs (borrowCode 0)
  have hp0 := h.prepare (borrowCode 0)
  have ip0 := inputs.prepare 0 (by decide)
  let w0 := world.allocate (.stack p0.frame 0 world.memory.length) (.node .tuple 0 [])
  let a0 : Activation := {p0 with roots := p0.roots.set 0 (some ⟨world.memory.length, world.memory.length⟩), state := p0.state.set 0 .empty}
  obtain ⟨r0, h0⟩ := hp0.storageLive (slot := 0) (by change 0 < active.count; omega)
    (by change active.roots 0 = none; exact unbound 0 (by simp))
  change LoanSafeMachine before callers previous external w0 a0 at h0
  have i0 : InputLocals left right table a0.state := ip0.set 0 .empty (by simp)
  let p4 := a0.forgetRefs (borrowCode 1)
  have hp4 := h0.prepare (borrowCode 1)
  have ip4 := i0.prepare 1 (by decide)
  let w4 := w0.allocate (.stack p4.frame 4 w0.memory.length) (.node .tuple 0 [])
  let a4 : Activation := {p4 with roots := p4.roots.set 4 (some ⟨w0.memory.length, w0.memory.length⟩), state := p4.state.set 4 .empty}
  obtain ⟨r4, h4⟩ := hp4.storageLive (slot := 4) (by change 4 < active.count; omega)
    (by simpa [p4, a0, p0, Activation.forgetRefs, Roots.set] using unbound 4 (by simp))
  change LoanSafeMachine before callers previous external w4 a4 at h4
  have i4 : InputLocals left right table a4.state := ip4.set 4 .empty (by simp)
  let p5 := a4.forgetRefs (borrowCode 2)
  have hp5 := h4.prepare (borrowCode 2)
  have ip5 := i4.prepare 2 (by decide)
  let w5 := w4.allocate (.stack p5.frame 5 w4.memory.length) (.node .tuple 0 [])
  let a5 : Activation := {p5 with roots := p5.roots.set 5 (some ⟨w4.memory.length, w4.memory.length⟩), state := p5.state.set 5 .empty}
  obtain ⟨r5, h5⟩ := hp5.storageLive (slot := 5) (by change 5 < active.count; omega)
    (by simpa [p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set] using unbound 5 (by simp))
  change LoanSafeMachine before callers previous external w5 a5 at h5
  have i5 : InputLocals left right table a5.state := ip5.set 5 .empty (by simp)
  let p6 := a5.forgetRefs (borrowCode 3)
  have hp6 := h5.prepare (borrowCode 3)
  have ip6 := i5.prepare 3 (by decide)
  let w6 := w5.allocate (.stack p6.frame 6 w5.memory.length) (.node .tuple 0 [])
  let a6 : Activation := {p6 with roots := p6.roots.set 6 (some ⟨w5.memory.length, w5.memory.length⟩), state := p6.state.set 6 .empty}
  obtain ⟨r6, h6⟩ := hp6.storageLive (slot := 6) (by change 6 < active.count; omega)
    (by simpa [p6, a5, p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set] using unbound 6 (by simp))
  change LoanSafeMachine before callers previous external w6 a6 at h6
  have i6 : InputLocals left right table a6.state := ip6.set 6 .empty (by simp)
  have read4 : w6.memory[w0.memory.length]? = some (.node .tuple 0 []) :=
    (w5.allocate_keeps h5.wellFormed _ _ []).memory _ _
      ((w4.allocate_keeps h4.wellFormed _ _ []).memory _ _ (w0.allocate_spec _ _).2.1)
  have read5 : w6.memory[w4.memory.length]? = some (.node .tuple 0 []) :=
    (w5.allocate_keeps h5.wellFormed _ _ []).memory _ _ (w4.allocate_spec _ _).2.1
  have empty4 : a6.state 4 = .empty := by
    simp only [a6, Partial.Locals.set, show (4 : Nat) ≠ 6 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a5, Partial.Locals.set, show (4 : Nat) ≠ 5 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a4, Partial.Locals.set, ite_true]
  have empty5 : a6.state 5 = .empty := by
    simp only [a6, Partial.Locals.set, show (5 : Nat) ≠ 6 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a5, Partial.Locals.set, ite_true]
  refine ⟨w6, a6, ⟨world.memory.length, world.memory.length⟩, ⟨w0.memory.length, w0.memory.length⟩,
    ⟨w4.memory.length, w4.memory.length⟩, ⟨w5.memory.length, w5.memory.length⟩,
    .cons (Calling.instruction_noncall_run (act := .storageLive 0) r0)
      (.cons (Calling.instruction_noncall_run (act := .storageLive 4) r4)
        (.cons (Calling.instruction_noncall_run (act := .storageLive 5) r5)
          (.cons (Calling.instruction_noncall_run (act := .storageLive 6) r6) (.nil _ _)))),
    h6, i6, rfl, ?_, ?_, ?_, ?_, read4, read5, (w5.allocate_spec _ _).2.1,
    empty4, empty5, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [a6, p6, a5, p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set]
  · simp [a6, p6, a5, p5, a4, p4, Roots.set, Activation.forgetRefs]
  · simp [a6, p6, a5, p5, Roots.set, Activation.forgetRefs]
  · simp [a6, Roots.set]
  · simp [a6, Partial.Locals.set]
  · simpa [a6, p6, a5, p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set] using unbound 7 (by simp)
  · simpa [a6, p6, a5, p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set] using unbound 8 (by simp)
  · exact (w5.allocate_keeps h5.wellFormed _ _ []).memory _ _
      ((w4.allocate_keeps h4.wellFormed _ _ []).memory _ _
        ((w0.allocate_keeps h0.wellFormed _ _ []).memory _ _ (world.allocate_spec _ _).2.1))
  · intro index member
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at member
    simp only [a6, p6, a5, p5, a4, p4, a0, p0, Activation.forgetRefs, Roots.set,
      member.1, member.2.1, member.2.2.1, member.2.2.2, ite_false]
  · simp only [a6, Partial.Locals.set, show (0 : Nat) ≠ 6 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a5, Partial.Locals.set, show (0 : Nat) ≠ 5 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a4, Partial.Locals.set, show (0 : Nat) ≠ 4 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a0, Partial.Locals.set, ite_true]
  · intro queries
    have q0 := (queries.prepare (borrowCode 0)).allocate hp0.wellFormed 0 (by decide)
    change QueryOrigins w0 a0 before.memory.length at q0
    have q4 := (q0.prepare (borrowCode 1)).allocate hp4.wellFormed 4 (by decide)
    change QueryOrigins w4 a4 before.memory.length at q4
    have q5 := (q4.prepare (borrowCode 2)).allocate hp5.wellFormed 5 (by decide)
    change QueryOrigins w5 a5 before.memory.length at q5
    exact (q5.prepare (borrowCode 3)).allocate hp6.wellFormed 6 (by decide)

end SubtreeProofs.Rust.SourceEval.Evaluator
