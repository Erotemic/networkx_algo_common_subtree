module

public import SubtreeProofs.Rust.SourcePairTailScopeEntry
import Mathlib.Tactic.IntervalCases

/-! The actual successful-tail score prefix and its first six instructions.
Both owned native embeddings remain available for the scalar score calls. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def scoreCases : Code := .switch (.discriminant (.local 52)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none subtotalOverflow addRoot cleanupTails

def scoreActions : List Action :=
  [.storageLive 48, .assign 48 (.use (.move (.field (.local 41) (some 1) 0))),
   .assign 47 (.use (.move (.local 48))), .drop 48, .storageDead 48, .fakeRead (.local 47),
   .storageLive 51, .storageLive 52, .storageLive 53,
   .assign 53 (.use (.copy (.field (.local 37) none 1))), .storageLive 54,
   .assign 54 (.use (.copy (.field (.local 47) none 1))),
   .call .checkedAdd [.move (.local 53), .move (.local 54)] 52,
   .storageDead 54, .storageDead 53]

def scoreCode (index : Nat) : Code := (scoreActions.drop index).foldr Control.Tree.step scoreCases

theorem addScores_actions : addScores = scoreActions.foldr Control.Tree.step scoreCases := rfl

theorem score_tail_payload_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {heads tails : CommonEmbedding} {table : MemoTable}
    (scope : PairTailScope initial lh lt rh rt heads (some tails) table world active)
    (count : 49 ≤ active.count) (unbound48 : active.roots 48 = none) :
    ∃ final after,
      Calling.Prefix callee callers (scoreCode 6) (scoreActions.take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      after.roots = active.roots ∧ after.count = active.count ∧ after.frame = active.frame ∧
      after.state 41 = headPayloadHole ∧ after.state 47 = Slot.ofValue (encodeResult tails) ∧
      after.state 37 = Slot.ofValue (encodeResult heads) ∧
      after.state 42 = Slot.ofValue (encodeTable table) ∧
      after.state 28 = .shared (.boxed (encodeWord lt)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      (∀ slot binding, slot ≠ 47 → active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w48, a48, first, m48, roots48, count48, frame48, hole41, value48, memory48⟩ :=
    original_project_view_complete h callee (scoreCode 2) (source := 41) (destination := 48) (place := .field (.local 41) (some 1) 0)
      (by decide) (by decide) (by decide) rfl trivial (by rw [scope.result]; exact head_payload_take tails)
      headPayloadHole_typed (.adt .optional) (result_typed tails) (.adt .embedding) (by omega) unbound48
  obtain ⟨root47, bound47, raw47⟩ := scope.payloadRoot
  have bound47a48 : a48.roots 47 = some root47 := by simpa [roots48, Roots.set] using bound47
  let prepared := a48.forgetRefs (scoreCode 2)
  have machine := m48.prepare (scoreCode 2)
  have value : prepared.state 48 = Slot.ofValue (encodeResult tails) := (m48.prepare_closed_local _ 48 (by decide)).trans value48
  have empty47 : (prepared.state.set 48 .empty) 47 = .empty := by
    simp only [Partial.Locals.set, show (47 : Nat) ≠ 48 by decide, ite_false]
    rw [m48.prepare_closed_local _ 47 (by decide)]
    exact (first.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.payloadEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.payloadEmpty
  obtain ⟨cell47, assign47, afterMachine⟩ := machine.assign_empty bound47a48 (by decide) (memory48 47 root47 bound47 _ raw47)
    (use_local_source (state := prepared.state) (slot := 48) (by rw [value]; exact Slot.materialize_ofValue _)) empty47
    (machine.closed.clear 48)
    (by intro index member
        simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [Partial.Locals.set, prepared])
    trivial (result_typed tails) (.adt .embedding)
  let wa := w48.write root47.address cell47
  let aa : Activation := {prepared with state := (prepared.state.set 48 .empty).set 47 (Slot.ofValue (encodeResult tails))}
  change OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] wa aa at afterMachine
  have bound48 : aa.roots 48 = some ⟨world.memory.length, world.memory.length⟩ := by simp [aa, prepared, Activation.forgetRefs, roots48, Roots.set]
  have plan : RetirementPlan aa.roots [.drop 48, .storageDead 48] (aa.roots.set 48 none) := .drop bound48 (.dead bound48 (.nil _))
  have zero : ZeroRetirement [.drop 48, .storageDead 48] aa.state := by
    intro slot member
    have same : slot = 48 := by simpa using member
    subst slot; simp [aa, Partial.Locals.set, Slot.dropWork]
  obtain ⟨final, ar, retire, mr, rootsR, countR, memoryR⟩ := plan.complete_original callee (scoreCode 5) afterMachine rfl zero
  let after := ar.forgetRefs (scoreCode 5)
  have finalMachine := mr.prepare (scoreCode 5)
  have last3 : Calling.Prefix callee callers (scoreCode 6) ((scoreActions.drop 3).take 3) wa aa final after :=
    Calling.Prefix.append (suffix := scoreCode 6) (rest := [.fakeRead (.local 47)]) retire
      (.cons (Calling.instruction_noncall_run (act := .fakeRead (.local 47)) rfl) (.nil _ _))
  have last4 : Calling.Prefix callee callers (scoreCode 6) ((scoreActions.drop 2).take 4) w48 a48 final after :=
    .cons (Calling.instruction_noncall_run (act := .assign 47 (.use (.move (.local 48)))) assign47) last3
  have whole : Calling.Prefix callee callers (scoreCode 6) (scoreActions.take 6) world active final after :=
    Calling.Prefix.append (suffix := scoreCode 6) (rest := (scoreActions.drop 2).take 4) first last4
  have value47 : aa.state 47 = Slot.ofValue (encodeResult tails) := by simp only [aa, Partial.Locals.set, ite_true]
  refine ⟨final, after, whole, finalMachine, ?_, (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).2,
    (whole.frame_count h.native.valid h.native.callersValid h.native.wellFormed (by decide +kernel)).1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change ar.roots = active.roots
    rw [rootsR]
    funext slot
    by_cases same : slot = 48
    · subst slot; simpa [Roots.set] using unbound48.symm
    · simp [aa, prepared, Activation.forgetRefs, roots48, Roots.set, same]
  · exact (last4.closed_local_same (index := 41) m48.native.valid m48.native.callersValid m48.native.wellFormed
      (by rw [hole41]; exact headPayloadHole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans hole41
  · exact (last3.closed_local_same (index := 47) afterMachine.native.valid afterMachine.native.callersValid afterMachine.native.wellFormed
      (by rw [value47]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans value47
  · exact (whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.heads]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.heads
  · exact (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.table]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.table
  · exact (whole.observed_local_same (index := 28) h.native.valid h.native.callersValid h.native.wellFormed
      (by intro offset bound; change offset < 6 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans scope.leftTail
  · exact (whole.observed_local_same (index := 30) h.native.valid h.native.callersValid h.native.wellFormed
      (by intro offset bound; change offset < 6 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans scope.rightTail
  · intro slot binding different root raw read
    have not48 : slot ≠ 48 := by intro same; subst slot; rw [unbound48] at root; cases root
    have rootA48 : a48.roots slot = some binding := by simpa only [roots48, Roots.set, not48, ite_false] using root
    rw [memoryR]
    exact Activation.write_other_root machine.native.valid bound47a48 rootA48 (Ne.symm different) (memory48 slot binding root raw read) cell47

end SubtreeProofs.Rust.SourceEval.Evaluator
