module

public import SubtreeProofs.Rust.SourceOriginalConstantView
public import SubtreeProofs.Rust.SourceOriginalRetirement
public import SubtreeProofs.Rust.SourcePrefixFrame
public import SubtreeProofs.Rust.SourceCacheHitTransfer

/-! The shared nine-instruction failure output pattern of the pinned evaluator.
It returns None with the actual updated table, through the real temporaries,
guarded output assignment, destructor visits and storage retirement. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def failurePackActions (source optional table : Nat) : List Action :=
  [.storageLive optional, .assign optional (.aggregate .optional 0 []),
   .storageLive table, .assign table (.use (.move (.local source))),
   .assign 0 (.aggregate .tuple 0 [.move (.local optional), .move (.local table)]),
   .drop table, .storageDead table, .drop optional, .storageDead optional]

def failurePackCode (source optional table index : Nat) : Code :=
  ((failurePackActions source optional table).drop index).foldr Control.Tree.step .done

theorem headsFailure_actions : headsFailure = (failurePackActions 32 39 40).foldr Control.Tree.step .done := rfl

theorem failure_pack_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees)
    (source optional table : Nat) (sourceOutside : source ∉ exceptions) (optionOutside : optional ∉ exceptions)
    (tableOutside : table ∉ exceptions) (zeroOutside : 0 ∉ exceptions)
    (sourceNonzero : source ≠ 0) (optionNonzero : optional ≠ 0) (tableNonzero : table ≠ 0)
    (sourceOption : source ≠ optional) (sourceTable : source ≠ table) (optionTable : optional ≠ table)
    (optionBound : optional < active.count) (tableBound : table < active.count)
    (optionUnbound : active.roots optional = none) (tableUnbound : active.roots table = none)
    {nativeTable : MemoTable} (input : active.state source = Slot.ofValue (encodeTable nativeTable))
    {root0 : Binding} (bound0 : active.roots 0 = some root0) (raw0 : world.memory[root0.address]? = some (.node .tuple 0 []))
    (empty0 : active.state 0 = .empty) :
    ∃ final after,
      Calling.Prefix callee callers .done (failurePackActions source optional table) world active final after ∧
      OriginalLoanMachine before callers previous external exceptions final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 0 = Slot.ofValue (encodeOutput none nativeTable) ∧ after.state source = .empty := by
  obtain ⟨wo, ao, optionRun, mo, optionRoots, optionCount, optionFrame, optionValue, optionMemory⟩ :=
    original_constant_view_complete h callee (failurePackCode source optional table 2) optionOutside .optional 0
      (option_typed none) (.adt .optional) optionBound optionUnbound
  have sourceValue : ao.state source = Slot.ofValue (encodeTable nativeTable) := by
    have same := optionRun.closed_local_same (index := source) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [input]; exact ofValue_typed (table_typed nativeTable)) (.adt .table) rfl
      (by simp [LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operands, sourceOption])
    exact same.trans input
  obtain ⟨wt, tableActive, tableRun, mt, tableRoots, tableCount, tableFrame, sourceEmpty, tableValue, tableMemory⟩ :=
    original_move_view_complete mo callee (failurePackCode source optional table 4) sourceOutside tableOutside sourceValue
      (table_typed nativeTable) (.adt .table) (by rw [optionCount]; exact tableBound)
      (by simpa [optionRoots, Roots.set, Ne.symm optionTable] using tableUnbound)
  have first4 : Calling.Prefix callee callers (failurePackCode source optional table 4)
      ((failurePackActions source optional table).take 4) world active wt tableActive :=
    Calling.Prefix.append (suffix := failurePackCode source optional table 4)
      (rest := [.storageLive table, .assign table (.use (.move (.local source)))]) optionRun tableRun
  have bound0O : ao.roots 0 = some root0 := by simpa [optionRoots, Roots.set, Ne.symm optionNonzero] using bound0
  have bound0T : tableActive.roots 0 = some root0 := by simpa [tableRoots, Roots.set, Ne.symm tableNonzero] using bound0O
  have raw0T := tableMemory 0 root0 bound0O _ (optionMemory 0 root0 bound0 _ raw0)
  let prepared := tableActive.forgetRefs (failurePackCode source optional table 4)
  have machine := mt.prepare (failurePackCode source optional table 4)
  have optionT : tableActive.state optional = Slot.ofValue (encodeOption none) := by
    exact (tableRun.closed_local_same (index := optional) mo.native.valid mo.native.callersValid mo.native.wellFormed
      (by rw [optionValue]; exact ofValue_typed (option_typed none)) (.adt .optional) rfl
      (by simp [LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, splitPlace, optionTable, Ne.symm sourceOption])).trans optionValue
  have first : prepared.state optional = Slot.ofValue (encodeOption none) := (mt.prepare_closed_local _ optional optionOutside).trans optionT
  have second : prepared.state table = Slot.ofValue (encodeTable nativeTable) := (mt.prepare_closed_local _ table tableOutside).trans tableValue
  have emptyReturn : ((prepared.state.set optional .empty).set table .empty) 0 = .empty := by
    simp only [Partial.Locals.set, Ne.symm tableNonzero, Ne.symm optionNonzero, ite_false]
    rw [mt.prepare_closed_local _ 0 zeroOutside]
    exact (first4.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [empty0]; exact .empty .u32) .u32 rfl
      (by simp [failurePackActions, LocalPreservation.action, LocalPreservation.expression, LocalPreservation.operand, LocalPreservation.operands, splitPlace,
        Ne.symm optionNonzero, Ne.symm tableNonzero, Ne.symm sourceNonzero])).trans empty0
  obtain ⟨cell0, assign0, finalMachine⟩ := machine.assign_empty bound0T zeroOutside raw0T
    (aggregate_two_source (state := prepared.state) (first := optional) (second := table)
      (by rw [first]; exact Slot.materialize_ofValue _) (by rw [second]; exact Slot.materialize_ofValue _) (Ne.symm optionTable) .tuple 0)
    emptyReturn ((machine.closed.clear optional).clear table)
    (by intro index member
        have notO : index ≠ optional := by intro same; subst index; exact optionOutside member
        have notT : index ≠ table := by intro same; subst index; exact tableOutside member
        simp only [Partial.Locals.set, notO, notT, ite_false, prepared])
    (by intro op member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member; rcases member with rfl | rfl <;> trivial)
    (encodeOutput_typed none nativeTable) (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil)))
  let w0 := wt.write root0.address cell0
  let a0 : Activation := {prepared with state := ((prepared.state.set optional .empty).set table .empty).set 0 (Slot.ofValue (encodeOutput none nativeTable))}
  change OriginalLoanMachine before callers previous external exceptions w0 a0 at finalMachine
  have boundT : a0.roots table = some ⟨wo.memory.length, wo.memory.length⟩ := by simp [a0, prepared, Activation.forgetRefs, tableRoots, Roots.set]
  have boundO : a0.roots optional = some ⟨world.memory.length, world.memory.length⟩ := by
    simp [a0, prepared, Activation.forgetRefs, tableRoots, optionRoots, Roots.set, optionTable]
  have plan : RetirementPlan a0.roots [.drop table, .storageDead table, .drop optional, .storageDead optional]
      ((a0.roots.set table none).set optional none) :=
    .drop boundT (.dead boundT (.drop (binding := ⟨world.memory.length, world.memory.length⟩)
      (by simpa [Roots.set, optionTable] using boundO) (.dead (binding := ⟨world.memory.length, world.memory.length⟩)
        (by simpa [Roots.set, optionTable] using boundO) (.nil _))))
  have zero : ZeroRetirement [.drop table, .storageDead table, .drop optional, .storageDead optional] a0.state := by
    intro index member
    have selected : index = table ∨ index = optional := by simpa using member
    rcases selected with rfl | rfl <;> simp [a0, Partial.Locals.set, tableNonzero, optionNonzero, optionTable, Slot.dropWork]
  obtain ⟨final, after, cleanup, afterMachine, rootsAfter, countAfter, memoryAfter⟩ := plan.complete_original callee .done finalMachine rfl zero
  have last5 : Calling.Prefix callee callers .done ((failurePackActions source optional table).drop 4) wt tableActive final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 0 (.aggregate .tuple 0 [.move (.local optional), .move (.local table)])) assign0) cleanup
  have whole : Calling.Prefix callee callers .done (failurePackActions source optional table) world active final after :=
    Calling.Prefix.append (suffix := .done) (rest := (failurePackActions source optional table).drop 4) first4 last5
  have output0 : a0.state 0 = Slot.ofValue (encodeOutput none nativeTable) := by simp only [a0, Partial.Locals.set, ite_true]
  have zeroSource : a0.state source = .empty := by
    simp only [a0, Partial.Locals.set, sourceNonzero, sourceTable, sourceOption, ite_false]
    exact (mt.prepare_closed_local _ source sourceOutside).trans sourceEmpty
  refine ⟨final, after, whole, afterMachine, ?_, (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed rfl).2,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed rfl).1, ?_, ?_⟩
  · rw [rootsAfter]
    funext index
    by_cases isO : index = optional
    · subst index; simp [Roots.set, optionUnbound]
    by_cases isT : index = table
    · subst index; simp [Roots.set, tableUnbound, Ne.symm optionTable]
    · simp [a0, prepared, Activation.forgetRefs, tableRoots, optionRoots, Roots.set, isO, isT]
  · exact (cleanup.closed_local_same (index := 0) finalMachine.native.valid finalMachine.native.callersValid finalMachine.native.wellFormed
      (by rw [output0]; exact ofValue_typed (encodeOutput_typed none nativeTable))
      (.tuple (.cons (.adt .optional) (.cons (.adt .table) .nil))) rfl
      (by simp [LocalPreservation.action, Ne.symm optionNonzero, Ne.symm tableNonzero])).trans output0
  · exact (cleanup.closed_local_same (index := source) finalMachine.native.valid finalMachine.native.callersValid finalMachine.native.wellFormed
      (by rw [zeroSource]; exact .empty .u32) .u32 rfl
      (by simp [LocalPreservation.action, sourceOption, sourceTable])).trans zeroSource

end SubtreeProofs.Rust.SourceEval.Evaluator
