module

public import SubtreeProofs.Rust.SourceCacheHitScope

/-! Construct the two real cache-hit table/output assignments. The table moves
through its actual local root while query references may still alias its owned
data. Query read origins discharge the selected stack-root move guard. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem encodeOutput_typed (result : Option CommonEmbedding) (table : MemoTable) :
    SnapshotTyped (encodeOutput result table) (.tuple [.adt .optional, .adt .table]) :=
  .node (.tuple _) (.cons (option_typed result) (.cons (table_typed table) .nil))

theorem hit_transfer_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    (result : CommonEmbedding) (table : MemoTable)
    {root0 root12 : Binding} (returnBinding : active.roots 0 = some root0) (tableBinding : active.roots 12 = some root12)
    (returnMemory : world.memory[root0.address]? = some (.node .tuple 0 []))
    (tableMemory : world.memory[root12.address]? = some (.node .tuple 0 []))
    (empty0 : active.state 0 = .empty) (empty12 : active.state 12 = .empty)
    (tableValue : active.state 3 = Slot.ofValue (encodeTable table))
    (resultValue : active.state 10 = Slot.ofValue (encodeOption (some result))) :
    ∃ final after,
      Calling.Prefix callee callers (hitCode 11) ((hitActions.drop 9).take 2) world active final after ∧
      QueryMachine before callers previous external final after ∧ after.roots = active.roots ∧ after.count = active.count ∧
      after.state 0 = Slot.ofValue (encodeOutput (some result) table) ∧ after.state 3 = .empty ∧
      after.state 10 = .empty ∧ after.state 12 = .empty := by
  let p9 := active.forgetRefs (hitCode 9)
  have m9 := h.prepare (hitCode 9)
  have ready3 : p9.state 3 = Slot.ofValue (encodeTable table) := (h.prepare_closed_local _ 3 (by decide)).trans tableValue
  have uninitialized12 : (p9.state.set 3 .empty) 12 = .empty := by
    simpa only [Partial.Locals.set, show (12 : Nat) ≠ 3 by decide, ite_false] using
      (h.prepare_closed_local (hitCode 9) 12 (by decide)).trans empty12
  obtain ⟨cell12, assign12, m12⟩ := m9.assign_empty tableBinding (by decide) tableMemory
    (use_local_source (by rw [ready3]; exact Slot.materialize_ofValue _)) uninitialized12 (m9.closed.clear 3)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set]) trivial (table_typed table) (.adt .table)
  let w12 := world.write root12.address cell12
  let a12 : Activation := {p9 with state := (p9.state.set 3 .empty).set 12 (Slot.ofValue (encodeTable table))}
  change QueryMachine before callers previous external w12 a12 at m12
  have read0 : w12.memory[root0.address]? = some (.node .tuple 0 []) :=
    Activation.write_other_root m9.native.valid tableBinding returnBinding (by decide) returnMemory cell12
  let p10 := a12.forgetRefs (hitCode 10)
  have m10 := m12.prepare (hitCode 10)
  have ready10 : p10.state 10 = Slot.ofValue (encodeOption (some result)) := by
    calc
      p10.state 10 = a12.state 10 := m12.prepare_closed_local _ _ (by decide)
      _ = p9.state 10 := by simp only [a12, Partial.Locals.set, show (10 : Nat) ≠ 12 by decide,
        show (10 : Nat) ≠ 3 by decide, ite_false]
      _ = active.state 10 := h.prepare_closed_local _ _ (by decide)
      _ = _ := resultValue
  have ready12 : p10.state 12 = Slot.ofValue (encodeTable table) := by
    rw [m12.prepare_closed_local _ 12 (by decide)]
    simp only [a12, Partial.Locals.set, ite_true]
  have returnEmpty : ((p10.state.set 10 .empty).set 12 .empty) 0 = .empty := by
    simp only [Partial.Locals.set, show (0 : Nat) ≠ 12 by decide, show (0 : Nat) ≠ 10 by decide, ite_false]
    rw [m12.prepare_closed_local _ 0 (by decide)]
    simp only [a12, Partial.Locals.set, show (0 : Nat) ≠ 12 by decide, show (0 : Nat) ≠ 3 by decide, ite_false]
    exact (h.prepare_closed_local _ 0 (by decide)).trans empty0
  obtain ⟨cell0, assign0, finalMachine⟩ := m10.assign_empty returnBinding (by decide) read0
    (aggregate_two_source (by rw [ready10]; exact Slot.materialize_ofValue _)
      (by rw [ready12]; exact Slot.materialize_ofValue _) (by decide) .tuple 0)
    returnEmpty ((m10.closed.clear 10).clear 12)
    (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> simp [Partial.Locals.set])
    (by intro op member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl <;> trivial)
    (encodeOutput_typed (some result) table) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
  let final := w12.write root0.address cell0
  let after : Activation := {p10 with state := ((p10.state.set 10 .empty).set 12 .empty).set 0 (Slot.ofValue (encodeOutput (some result) table))}
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .assign 12 (.use (.move (.local 3)))) assign12)
      (.cons (Calling.instruction_noncall_run (act := .assign 0 (.aggregate .tuple 0 [.move (.local 10), .move (.local 12)])) assign0) (.nil _ _)),
    finalMachine, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · simp only [after, Partial.Locals.set, ite_true]
  · simp only [after, Partial.Locals.set, show (3 : Nat) ≠ 0 by decide, show (3 : Nat) ≠ 12 by decide,
      show (3 : Nat) ≠ 10 by decide, ite_false]
    rw [m12.prepare_closed_local _ 3 (by decide)]
    simp only [a12, Partial.Locals.set, show (3 : Nat) ≠ 12 by decide, ite_false, ite_true]
  · simp [after, Partial.Locals.set]
  · simp [after, Partial.Locals.set]

end SubtreeProofs.Rust.SourceEval.Evaluator
