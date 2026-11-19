module

public import SubtreeProofs.Rust.SourceEvaluatorStoragePrefix
public import SubtreeProofs.Rust.SourceNativeStorageRetirement

/-! Construct both actual table-reference assignments in the common evaluator
prelude. The table stays owned while its two shared views may alias it and each
other. Native referent structure discharges both fresh destination guards. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem table_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    (left right : BalancedWord) (table : MemoTable) (inputs : InputLocals left right table active.state)
    {resultRoot firstView secondView : Binding}
    (resultBinding : active.roots 4 = some resultRoot) (firstBinding : active.roots 5 = some firstView)
    (secondBinding : active.roots 6 = some secondView)
    (resultMemory : world.memory[resultRoot.address]? = some (.node .tuple 0 []))
    (firstMemory : world.memory[firstView.address]? = some (.node .tuple 0 []))
    (secondMemory : world.memory[secondView.address]? = some (.node .tuple 0 []))
    (resultEmpty : active.state 4 = .empty) (firstEmpty : active.state 5 = .empty) (secondEmpty : active.state 6 = .empty) :
    ∃ final after,
      Calling.Prefix callee callers (borrowCode 6)
        [.assign 6 (.address (.local 3)), .assign 5 (.address (.deref (.local 6)))] world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.state 4 = .empty ∧
      after.state 5 = .shared (encodeTable table) ∧ final.memory[resultRoot.address]? = some (.node .tuple 0 []) ∧
      after.state 6 = .shared (encodeTable table) ∧
      (∃ pointer, final.memory[secondView.address]? = some (.shared pointer)) ∧
      (∀ index binding, index ≠ 5 → index ≠ 6 → active.roots index = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) ∧
      (∀ index, index ≠ 5 → index ≠ 6 → active.state index = .empty → after.state index = .empty) ∧
      (QueryOrigins world active before.memory.length → QueryOrigins final after before.memory.length) := by
  let p6 := active.forgetRefs (borrowCode 4)
  have hp6 := h.prepare (borrowCode 4)
  have ip6 := inputs.prepare 4 (by decide)
  have source6 : SourceEval.expression p6.state (.address (.local 3)) = some (.reference (encodeTable table), p6.state) :=
    address_local_source (by rw [ip6.table]; exact Slot.materialize_ofValue _)
  have empty6 : p6.state 6 = .empty := LoanEnding.forget_empty _ _ secondEmpty
  have safeValue : LoanSafe (Slot.ofValue (.reference (encodeTable table))) := by
    simpa only [Slot.ofValue] using LoanSafe.shared (NativeData.table table)
  obtain ⟨cell6, r6, h6⟩ := hp6.assign_empty (slot := 6) (binding := secondView) secondBinding secondMemory
    source6 empty6 hp6.safe safeValue (by intros; trivial)
  let w6 := world.write secondView.address cell6
  let a6 : Activation := {p6 with state := p6.state.set 6 (Slot.ofValue (.reference (encodeTable table)))}
  change LoanSafeMachine before callers previous external w6 a6 at h6
  have i6 : InputLocals left right table a6.state := ip6.set 6 _ (by simp)
  have read4 : w6.memory[resultRoot.address]? = some (.node .tuple 0 []) :=
    Activation.write_other_root hp6.valid secondBinding resultBinding (by decide) resultMemory cell6
  have read5 : w6.memory[firstView.address]? = some (.node .tuple 0 []) :=
    Activation.write_other_root hp6.valid secondBinding firstBinding (by decide) firstMemory cell6
  let p5 := a6.forgetRefs (borrowCode 5)
  have hp5 := h6.prepare (borrowCode 5)
  have ip5 := i6.prepare 5 (by decide)
  have initialized6 : p5.state 6 = .shared (encodeTable table) := by
    rw [Activation.forgetRefs_observed a6 (borrowCode 5) 6 (by decide +kernel)]
    simp only [a6, Partial.Locals.set, ite_true, Slot.ofValue]
  have source5 := address_shared_source initialized6
  have empty5 : p5.state 5 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a6, Partial.Locals.set, show (5 : Nat) ≠ 6 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ firstEmpty
  obtain ⟨cell5, r5, h5⟩ := hp5.assign_empty (slot := 5) (binding := firstView) firstBinding read5
    source5 empty5 hp5.safe safeValue (by intros; trivial)
  let final := w6.write firstView.address cell5
  let after : Activation := {p5 with state := p5.state.set 5 (Slot.ofValue (.reference (encodeTable table)))}
  change LoanSafeMachine before callers previous external final after at h5
  have finalRead : final.memory[resultRoot.address]? = some (.node .tuple 0 []) :=
    Activation.write_other_root hp5.valid firstBinding resultBinding (by decide) read4 cell5
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .assign 6 (.address (.local 3))) r6)
      (.cons (Calling.instruction_noncall_run (act := .assign 5 (.address (.deref (.local 6)))) r5) (.nil _ _)),
    h5, ip5.set 5 _ (by simp), rfl, rfl, ?_, ?_, finalRead, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, show (4 : Nat) ≠ 5 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [a6, Partial.Locals.set, show (4 : Nat) ≠ 6 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ resultEmpty
  · simp only [after, Partial.Locals.set, ite_true, Slot.ofValue]
  · simpa only [after, Partial.Locals.set, show (6 : Nat) ≠ 5 by decide, ite_false] using initialized6
  · obtain ⟨pointer, memory⟩ := hp5.shared_root secondBinding initialized6
    exact ⟨pointer, Activation.write_other_root hp5.valid firstBinding secondBinding (by decide) memory cell5⟩
  · intro index binding five six hb raw memory
    have first := Activation.write_other_root hp6.valid secondBinding hb (Ne.symm six) memory cell6
    exact Activation.write_other_root hp5.valid firstBinding hb (Ne.symm five) first cell5
  · intro index five six empty
    simp only [after, Partial.Locals.set, five, ite_false]
    apply LoanEnding.forget_empty
    simp only [a6, Partial.Locals.set, six, ite_false]
    exact LoanEnding.forget_empty _ _ empty
  · intro queries
    have q6 := (queries.prepare (borrowCode 4)).write_other hp6.valid ip6.references secondBinding (by decide)
      (hp6.fresh 6 secondView secondBinding) cell6
    have qa6 := q6.set_other 6 (by decide) (Slot.ofValue (.reference (encodeTable table)))
    change QueryOrigins w6 a6 before.memory.length at qa6
    have q5 := (qa6.prepare (borrowCode 5)).write_other hp5.valid ip5.references firstBinding (by decide)
      (hp5.fresh 5 firstView firstBinding) cell5
    exact q5.set_other 5 (by decide) (Slot.ofValue (.reference (encodeTable table)))

end SubtreeProofs.Rust.SourceEval.Evaluator
