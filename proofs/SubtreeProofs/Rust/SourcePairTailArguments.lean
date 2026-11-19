module

public import SubtreeProofs.Rust.SourcePairTailProgram
public import SubtreeProofs.Rust.SourceOriginalMoveView
import Mathlib.Tactic.IntervalCases

/-! Construct the actual tail recursive-call destination, dereferenced query
arguments and owned table argument. This stops before the recursive call; its
success will be supplied by the induction on smaller native requests. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure TailArgumentScope (initial : Activation) (lh lt rh rt : BalancedWord) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  frame : active.frame = initial.frame
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  table : active.state 46 = Slot.ofValue (encodeTable table)
  left : active.state 44 = .shared (encodeWord lt)
  right : active.state 45 = .shared (encodeWord rt)
  result : ∃ binding, active.roots 43 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  resultEmpty : active.state 43 = .empty
  tableEmpty : active.state 32 = .empty
  bound : ∀ slot ∈ [43, 44, 45, 46], ∃ binding, active.roots slot = some binding
  otherRoots : ∀ slot, slot ∉ [43, 44, 45, 46] → active.roots slot = initial.roots slot

theorem pair_tail_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {table : MemoTable}
    (tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt))
    (left : active.state 28 = .shared (.boxed (encodeWord lt))) (right : active.state 30 = .shared (.boxed (encodeWord rt)))
    (tableValue : active.state 32 = Slot.ofValue (encodeTable table)) (count : 47 ≤ active.count)
    (unbound : ∀ slot ∈ [43, 44, 45, 46], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (tailCode 13) ((tailActions.drop 6).take 7) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      TailArgumentScope active lh lt rh rt table final after ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let prepared := active.forgetRefs (tailCode 6)
  have machine := h.prepare (tailCode 6)
  let root43 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w43 := world.allocate (.stack prepared.frame 43 world.memory.length) (.node .tuple 0 [])
  let a43 : Activation := {prepared with roots := prepared.roots.set 43 (some root43), state := prepared.state.set 43 .empty}
  obtain ⟨live43, m43⟩ := machine.storageLive (slot := 43) (by change 43 < active.count; omega) (unbound 43 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] w43 a43 at m43
  have left43 : a43.state 28 = .shared (.boxed (encodeWord lt)) := by
    simp only [a43, Partial.Locals.set, show (28 : Nat) ≠ 43 by decide, ite_false]
    exact (Activation.forgetRefs_observed active (tailCode 6) 28 (by decide +kernel)).trans left
  obtain ⟨w44, a44, run44, m44, roots44, count44, frame44, value44, memory44⟩ :=
    original_borrow_view_complete m43 callee (tailCode 9) (slot := 28) (destination := 44) (by simp) (by decide) rfl
      (by rw [left43]; exact .shared _ _) (boxed_word_reborrow_source left43) (NativeData.word lt)
      (by change 44 < active.count; omega)
      (by simpa [a43, prepared, Activation.forgetRefs, Roots.set] using unbound 44 (by simp))
  have right43 : a43.state 30 = .shared (.boxed (encodeWord rt)) := by
    simp only [a43, Partial.Locals.set, show (30 : Nat) ≠ 43 by decide, ite_false]
    exact (Activation.forgetRefs_observed active (tailCode 6) 30 (by decide +kernel)).trans right
  have right44 : a44.state 30 = .shared (.boxed (encodeWord rt)) :=
    (run44.observed_local_same (index := 30) m43.native.valid m43.native.callersValid m43.native.wellFormed
      (by intro offset bound; change offset < 2 at bound; interval_cases offset <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)).trans right43
  obtain ⟨w45, a45, run45, m45, roots45, count45, frame45, value45, memory45⟩ :=
    original_borrow_view_complete m44 callee (tailCode 11) (slot := 30) (destination := 45) (by simp) (by decide) rfl
      (by rw [right44]; exact .shared _ _) (boxed_word_reborrow_source right44) (NativeData.word rt)
      (by rw [count44]; change 45 < active.count; omega)
      (by simpa [roots44, a43, prepared, Activation.forgetRefs, Roots.set] using unbound 45 (by simp))
  have first5 : Calling.Prefix callee callers (tailCode 11) ((tailActions.drop 6).take 5) world active w45 a45 :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 43) live43)
      (Calling.Prefix.append (suffix := tailCode 11) (rest := (tailActions.drop 9).take 2) run44 run45)
  have table45 : a45.state 32 = Slot.ofValue (encodeTable table) :=
    (first5.closed_local_same (index := 32) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans tableValue
  obtain ⟨final, after, transfer, finalMachine, roots46, count46, frame46, empty32, value46, memory46⟩ :=
    original_move_view_complete m45 callee (tailCode 13) (source := 32) (destination := 46) (by decide) (by decide)
      table45 (table_typed table) (.adt .table) (by rw [count45, count44]; change 46 < active.count; omega)
      (by simpa [roots45, roots44, a43, prepared, Activation.forgetRefs, Roots.set] using unbound 46 (by simp))
  have last4 : Calling.Prefix callee callers (tailCode 13) ((tailActions.drop 9).take 4) w44 a44 final after :=
    Calling.Prefix.append (suffix := tailCode 13) (rest := (tailActions.drop 11).take 2) run45 transfer
  have whole : Calling.Prefix callee callers (tailCode 13) ((tailActions.drop 6).take 7) world active final after :=
    Calling.Prefix.append (suffix := tailCode 13) (rest := (tailActions.drop 11).take 2) first5 transfer
  have root43a43 : a43.roots 43 = some root43 := by simp [a43, Roots.set]
  have root43a44 : a44.roots 43 = some root43 := by simpa [roots44, Roots.set] using root43a43
  have root43a45 : a45.roots 43 = some root43 := by simpa [roots45, Roots.set] using root43a44
  have root43After : after.roots 43 = some root43 := by simpa [roots46, Roots.set] using root43a45
  have raw43 : final.memory[root43.address]? = some (.node .tuple 0 []) :=
    memory46 43 root43 root43a45 _ (memory45 43 root43 root43a44 _ (memory44 43 root43 root43a43 _ (world.allocate_spec _ _).2.1))
  have empty43a43 : a43.state 43 = .empty := by simp only [a43, Partial.Locals.set, ite_true]
  have rest6 : Calling.Prefix callee callers (tailCode 13) ((tailActions.drop 7).take 6) w43 a43 final after :=
    Calling.Prefix.append (suffix := tailCode 13) (rest := (tailActions.drop 9).take 4) run44 last4
  refine ⟨final, after, whole, finalMachine, ?_, ?_⟩
  · refine ⟨count46.trans (count45.trans count44), frame46.trans (frame45.trans frame44), ?_, value46, ?_, ?_,
      ⟨root43, root43After, raw43⟩, ?_, empty32, ?_, ?_⟩
    · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple
    · exact (last4.observed_local_same (index := 44) m44.native.valid m44.native.callersValid m44.native.wellFormed
        (by intro offset bound; change offset < 4 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans value44
    · exact (transfer.observed_local_same (index := 45) m45.native.valid m45.native.callersValid m45.native.wellFormed
        (by intro offset bound; change offset < 2 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans value45
    · exact (rest6.closed_local_same (index := 43) m43.native.valid m43.native.callersValid m43.native.wellFormed
        (by rw [empty43a43]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty43a43
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [roots46, roots45, roots44, a43, Roots.set]
    · intro slot outside
      have different : slot ≠ 43 ∧ slot ≠ 44 ∧ slot ≠ 45 ∧ slot ≠ 46 := by simpa using outside
      simp only [roots46, roots45, roots44, a43, prepared, Roots.set, Activation.forgetRefs,
        different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · intro index binding root raw read
    have not43 : index ≠ 43 := by intro same; subst index; rw [unbound 43 (by simp)] at root; cases root
    have not44 : index ≠ 44 := by intro same; subst index; rw [unbound 44 (by simp)] at root; cases root
    have not45 : index ≠ 45 := by intro same; subst index; rw [unbound 45 (by simp)] at root; cases root
    have rootA43 : a43.roots index = some binding := by simpa only [a43, prepared, Activation.forgetRefs, Roots.set, not43, ite_false] using root
    have rootA44 : a44.roots index = some binding := by simpa only [roots44, Roots.set, not44, ite_false] using rootA43
    have rootA45 : a45.roots index = some binding := by simpa only [roots45, Roots.set, not45, ite_false] using rootA44
    exact memory46 index binding rootA45 raw (memory45 index binding rootA44 raw (memory44 index binding rootA43 raw
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read)))

end SubtreeProofs.Rust.SourceEval.Evaluator
