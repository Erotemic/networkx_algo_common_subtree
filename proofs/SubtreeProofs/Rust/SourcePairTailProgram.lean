module

public import SubtreeProofs.Rust.SourcePairHeadScopeEntry
import Mathlib.Tactic.IntervalCases

/-! The actual successful-head/tail-recursion instructions and native partial
head-result mask. The real tail-result switch and both continuations remain. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def tailCases : Code := .switch (.discriminant (.local 41)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none tailsFailure addScores cleanupHeads

def tailActions : List Action :=
  [.storageLive 38, .assign 38 (.use (.move (.field (.local 31) (some 1) 0))),
   .assign 37 (.use (.move (.local 38))), .drop 38, .storageDead 38, .fakeRead (.local 37),
   .storageLive 43, .storageLive 44, .assign 44 (.address (.deref (.deref (.local 28)))),
   .storageLive 45, .assign 45 (.address (.deref (.deref (.local 30)))),
   .storageLive 46, .assign 46 (.use (.move (.local 32))),
   .call .evaluate [.move (.local 44), .move (.local 45), .move (.local 46)] 43,
   .storageDead 46, .storageDead 45, .storageDead 44,
   .storageLive 41, .assign 41 (.use (.move (.field (.local 43) none 0))),
   .storageLive 42, .assign 42 (.use (.move (.field (.local 43) none 1))),
   .drop 43, .storageDead 43, .storageLive 47]

def tailCode (index : Nat) : Code := (tailActions.drop index).foldr Control.Tree.step tailCases

theorem recurseTails_actions : recurseTails = tailActions.foldr Control.Tree.step tailCases := rfl

def headPayloadHole : Slot := .node .optional 1 [.empty]

theorem head_payload_take (heads : CommonEmbedding) :
    (Slot.ofValue (encodeOption (some heads))).take [.field (some 1) 0] = some (encodeResult heads, headPayloadHole) := by
  simp [encodeOption, Slot.ofValue, ofFields, Slot.take, Slot.materialize_ofValue, headPayloadHole]

theorem headPayloadHole_typed : SlotTyped headPayloadHole (.adt .optional) := .node .some (.cons (.empty (.adt .embedding)) .nil)

theorem tail_head_payload_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads : CommonEmbedding} {table : MemoTable}
    (scope : PairHeadScope initial lh lt rh rt (some heads) table world active)
    (count : 39 ≤ active.count) (unbound38 : active.roots 38 = none) :
    ∃ final after,
      Calling.Prefix callee callers (tailCode 6) (tailActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 31 = headPayloadHole ∧ after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 32 = Slot.ofValue (encodeTable table) ∧
      after.state 28 = .shared (.boxed (encodeWord lt)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      (∀ slot binding, slot ≠ 37 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w38, a38, first, m38, roots38, count38, frame38, hole31, value38, memory38⟩ :=
    original_project_view_complete h callee (tailCode 2) (source := 31) (destination := 38) (place := .field (.local 31) (some 1) 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [scope.result]; exact head_payload_take heads)
      headPayloadHole_typed (.adt .optional) (result_typed heads) (.adt .embedding) (by omega) unbound38
  obtain ⟨root37, bound37, raw37⟩ := scope.payloadRoot
  have bound37a38 : a38.roots 37 = some root37 := by simpa [roots38, Roots.set] using bound37
  let prepared := a38.forgetRefs (tailCode 2)
  have machine := m38.prepare (tailCode 2)
  have value : prepared.state 38 = Slot.ofValue (encodeResult heads) := (m38.prepare_closed_local _ 38 (by decide)).trans value38
  have empty37 : (prepared.state.set 38 .empty) 37 = .empty := by
    simp only [Partial.Locals.set, show (37 : Nat) ≠ 38 by decide, ite_false]
    rw [m38.prepare_closed_local _ 37 (by decide)]
    exact (first.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.payloadEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.payloadEmpty
  obtain ⟨cell37, assign37, afterMachine⟩ := machine.assign_empty bound37a38 (by decide) (memory38 37 root37 bound37 _ raw37)
    (use_local_source (state := prepared.state) (slot := 38) (by rw [value]; exact Slot.materialize_ofValue _)) empty37
    (machine.closed.clear 38)
    (by intro index member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Partial.Locals.set, prepared])
    trivial (result_typed heads) (.adt .embedding)
  let wa := w38.write root37.address cell37
  let aa : Activation := {prepared with state := (prepared.state.set 38 .empty).set 37 (Slot.ofValue (encodeResult heads))}
  change OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] wa aa at afterMachine
  have bound38 : aa.roots 38 = some ⟨world.memory.length, world.memory.length⟩ := by simp [aa, prepared, Activation.forgetRefs, roots38, Roots.set]
  have plan : RetirementPlan aa.roots [.drop 38, .storageDead 38] (aa.roots.set 38 none) := .drop bound38 (.dead bound38 (.nil _))
  have zero : ZeroRetirement [.drop 38, .storageDead 38] aa.state := by
    intro slot member
    have same : slot = 38 := by simpa using member
    subst slot; simp [aa, Partial.Locals.set, Slot.dropWork]
  obtain ⟨final, ar, retire, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (tailCode 5) afterMachine rfl zero
  let after := ar.forgetRefs (tailCode 5)
  have finalMachine := mr.prepare (tailCode 5)
  have last3 : Calling.Prefix callee callers (tailCode 6) ((tailActions.drop 3).take 3) wa aa final after :=
    Calling.Prefix.append (suffix := tailCode 6) (rest := [.fakeRead (.local 37)]) retire
      (.cons (Calling.instruction_noncall_run (act := .fakeRead (.local 37)) rfl) (.nil _ _))
  have last4 : Calling.Prefix callee callers (tailCode 6) ((tailActions.drop 2).take 4) w38 a38 final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 37 (.use (.move (.local 38)))) assign37) last3
  have whole : Calling.Prefix callee callers (tailCode 6) (tailActions.take 6) world active final after :=
    Calling.Prefix.append (suffix := tailCode 6) (rest := (tailActions.drop 2).take 4) first last4
  have value37 : aa.state 37 = Slot.ofValue (encodeResult heads) := by simp only [aa, Partial.Locals.set, ite_true]
  refine ⟨final, after, whole, finalMachine, ?_, (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).2,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ar.roots = active.roots
    rw [rootsR]
    funext slot
    by_cases same : slot = 38
    · subst slot; simpa [Roots.set] using unbound38.symm
    · simp [aa, prepared, Activation.forgetRefs, roots38, Roots.set, same]
  · exact (last4.closed_local_same (index := 31) m38.native.valid m38.native.callersValid m38.native.wellFormed
      (by rw [hole31]; exact headPayloadHole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans hole31
  · exact (last3.closed_local_same (index := 37) afterMachine.native.valid afterMachine.native.callersValid afterMachine.native.wellFormed
      (by rw [value37]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value37
  · exact (whole.closed_local_same (index := 32) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.table]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.table
  · exact (whole.observed_local_same (index := 28) h.native.valid h.native.callersValid h.native.wellFormed
      (by intro offset bound; change offset < 6 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans scope.leftTail
  · exact (whole.observed_local_same (index := 30) h.native.valid h.native.callersValid h.native.wellFormed
      (by intro offset bound; change offset < 6 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans scope.rightTail
  · intro slot binding different root raw read
    have not38 : slot ≠ 38 := by intro same; subst slot; rw [unbound38] at root; cases root
    have rootA38 : a38.roots slot = some binding := by simpa only [roots38, Roots.set, not38, ite_false] using root
    rw [memoryR]
    exact Activation.write_other_root machine.native.valid bound37a38 rootA38 (Ne.symm different) (memory38 slot binding root raw read) cell37

end SubtreeProofs.Rust.SourceEval.Evaluator
