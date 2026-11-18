module

public import SubtreeProofs.Rust.SourcePairHeadViews
public import SubtreeProofs.Rust.SourceOriginalMoveView
import Mathlib.Tactic.IntervalCases

/-! Construct the actual head recursive-call destination, dereferenced query
arguments and owned table argument. This stops before the recursive call; its
success will be supplied by the induction on smaller native requests. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem boxed_word_reborrow_source {state : State} {slot : Nat} {word : BalancedWord}
    (initialized : state slot = .shared (.boxed (encodeWord word))) :
    state.read (.deref (.deref (.local slot))) = some (encodeWord word) := by
  simp only [Partial.Locals.read, splitPlace, List.nil_append, List.cons_append, initialized, Slot.read, Slot.get,
    Slot.ofValue, bind, Option.bind, Slot.materialize_ofValue]

structure HeadArgumentScope (initial : Activation) (lh lt rh rt : BalancedWord) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  frame : active.frame = initial.frame
  tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt)
  table : active.state 36 = Slot.ofValue (encodeTable table)
  left : active.state 34 = .shared (encodeWord lh)
  right : active.state 35 = .shared (encodeWord rh)
  result : ∃ binding, active.roots 33 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  resultEmpty : active.state 33 = .empty
  tableEmpty : active.state 3 = .empty
  bound : ∀ slot ∈ [33, 34, 35, 36], ∃ binding, active.roots slot = some binding
  otherRoots : ∀ slot, slot ∉ [33, 34, 35, 36] → active.roots slot = initial.roots slot

theorem pair_head_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [30, 29, 28, 27, 1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {table : MemoTable}
    (tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt))
    (left : active.state 27 = .shared (.boxed (encodeWord lh))) (right : active.state 29 = .shared (.boxed (encodeWord rh)))
    (tableValue : active.state 3 = Slot.ofValue (encodeTable table)) (count : 37 ≤ active.count)
    (unbound : ∀ slot ∈ [33, 34, 35, 36], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (headCode 15) ((headActions.drop 8).take 7) world active final after ∧
      OriginalLoanMachine before callers previous external [35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      HeadArgumentScope active lh lt rh rt table final after ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  let prepared := active.forgetRefs (headCode 8)
  have machine := h.prepare (headCode 8)
  let root33 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w33 := world.allocate (.stack prepared.frame 33 world.memory.length) (.node .tuple 0 [])
  let a33 : Activation := {prepared with roots := prepared.roots.set 33 (some root33), state := prepared.state.set 33 .empty}
  obtain ⟨live33, m33⟩ := machine.storageLive (slot := 33) (by change 33 < active.count; omega) (unbound 33 (by simp)) (by decide)
  change OriginalLoanMachine before callers previous external [30, 29, 28, 27, 1, 2, 13] w33 a33 at m33
  have left33 : a33.state 27 = .shared (.boxed (encodeWord lh)) := by
    simp only [a33, Partial.Locals.set, show (27 : Nat) ≠ 33 by decide, ite_false]
    exact (Activation.forgetRefs_observed active (headCode 8) 27 (head_observes_fields 27 (by simp))).trans left
  obtain ⟨w34, a34, run34, m34, roots34, count34, frame34, value34, memory34⟩ :=
    original_borrow_view_complete m33 callee (headCode 11) (slot := 27) (destination := 34) (by simp) (by decide) rfl
      (by rw [left33]; exact .shared _ _) (boxed_word_reborrow_source left33) (NativeData.word lh)
      (by change 34 < active.count; omega)
      (by simpa [a33, prepared, Activation.forgetRefs, Roots.set] using unbound 34 (by simp))
  have right33 : a33.state 29 = .shared (.boxed (encodeWord rh)) := by
    simp only [a33, Partial.Locals.set, show (29 : Nat) ≠ 33 by decide, ite_false]
    exact (Activation.forgetRefs_observed active (headCode 8) 29 (head_observes_fields 29 (by simp))).trans right
  have right34 : a34.state 29 = .shared (.boxed (encodeWord rh)) :=
    (run34.observed_local_same (index := 29) m33.native.valid m33.native.callersValid m33.native.wellFormed
      (by intro offset bound; change offset < 2 at bound; interval_cases offset <;> decide +kernel)
      (by decide +kernel) (by decide +kernel)).trans right33
  obtain ⟨w35, a35, run35, m35, roots35, count35, frame35, value35, memory35⟩ :=
    original_borrow_view_complete m34 callee (headCode 13) (slot := 29) (destination := 35) (by simp) (by decide) rfl
      (by rw [right34]; exact .shared _ _) (boxed_word_reborrow_source right34) (NativeData.word rh)
      (by rw [count34]; change 35 < active.count; omega)
      (by simpa [roots34, a33, prepared, Activation.forgetRefs, Roots.set] using unbound 35 (by simp))
  have first5 : Calling.Prefix callee callers (headCode 13) ((headActions.drop 8).take 5) world active w35 a35 :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 33) live33)
      (Calling.Prefix.append (suffix := headCode 13) (rest := (headActions.drop 11).take 2) run34 run35)
  have table35 : a35.state 3 = Slot.ofValue (encodeTable table) :=
    (first5.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans tableValue
  obtain ⟨final, after, transfer, finalMachine, roots36, count36, frame36, empty3, value36, memory36⟩ :=
    original_move_view_complete m35 callee (headCode 15) (source := 3) (destination := 36) (by decide) (by decide)
      table35 (table_typed table) (.adt .table) (by rw [count35, count34]; change 36 < active.count; omega)
      (by simpa [roots35, roots34, a33, prepared, Activation.forgetRefs, Roots.set] using unbound 36 (by simp))
  have last4 : Calling.Prefix callee callers (headCode 15) ((headActions.drop 11).take 4) w34 a34 final after :=
    Calling.Prefix.append (suffix := headCode 15) (rest := (headActions.drop 13).take 2) run35 transfer
  have whole : Calling.Prefix callee callers (headCode 15) ((headActions.drop 8).take 7) world active final after :=
    Calling.Prefix.append (suffix := headCode 15) (rest := (headActions.drop 13).take 2) first5 transfer
  have root33a33 : a33.roots 33 = some root33 := by simp [a33, Roots.set]
  have root33a34 : a34.roots 33 = some root33 := by simpa [roots34, Roots.set] using root33a33
  have root33a35 : a35.roots 33 = some root33 := by simpa [roots35, Roots.set] using root33a34
  have root33After : after.roots 33 = some root33 := by simpa [roots36, Roots.set] using root33a35
  have raw33 : final.memory[root33.address]? = some (.node .tuple 0 []) :=
    memory36 33 root33 root33a35 _ (memory35 33 root33 root33a34 _ (memory34 33 root33 root33a33 _ (world.allocate_spec _ _).2.1))
  have empty33a33 : a33.state 33 = .empty := by simp only [a33, Partial.Locals.set, ite_true]
  have rest6 : Calling.Prefix callee callers (headCode 15) ((headActions.drop 9).take 6) w33 a33 final after :=
    Calling.Prefix.append (suffix := headCode 15) (rest := (headActions.drop 11).take 4) run34 last4
  refine ⟨final, after, whole, finalMachine, ?_, ?_⟩
  · refine ⟨count36.trans (count35.trans count34), frame36.trans (frame35.trans frame34), ?_, value36, ?_, ?_,
      ⟨root33, root33After, raw33⟩, ?_, empty3, ?_, ?_⟩
    · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple
    · exact (last4.observed_local_same (index := 34) m34.native.valid m34.native.callersValid m34.native.wellFormed
        (by intro offset bound; change offset < 4 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans value34
    · exact (transfer.observed_local_same (index := 35) m35.native.valid m35.native.callersValid m35.native.wellFormed
        (by intro offset bound; change offset < 2 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)).trans value35
    · exact (rest6.closed_local_same (index := 33) m33.native.valid m33.native.callersValid m33.native.wellFormed
        (by rw [empty33a33]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty33a33
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [roots36, roots35, roots34, a33, Roots.set]
    · intro slot outside
      have different : slot ≠ 33 ∧ slot ≠ 34 ∧ slot ≠ 35 ∧ slot ≠ 36 := by simpa using outside
      simp only [roots36, roots35, roots34, a33, prepared, Roots.set, Activation.forgetRefs,
        different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · intro index binding root raw read
    have not33 : index ≠ 33 := by intro same; subst index; rw [unbound 33 (by simp)] at root; cases root
    have not34 : index ≠ 34 := by intro same; subst index; rw [unbound 34 (by simp)] at root; cases root
    have not35 : index ≠ 35 := by intro same; subst index; rw [unbound 35 (by simp)] at root; cases root
    have rootA33 : a33.roots index = some binding := by simpa only [a33, prepared, Activation.forgetRefs, Roots.set, not33, ite_false] using root
    have rootA34 : a34.roots index = some binding := by simpa only [roots34, Roots.set, not34, ite_false] using rootA33
    have rootA35 : a35.roots index = some binding := by simpa only [roots35, Roots.set, not35, ite_false] using rootA34
    exact memory36 index binding rootA35 raw (memory35 index binding rootA34 raw (memory34 index binding rootA33 raw
      ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read)))

theorem head_argument_fields_same {callee : Derived.Callees} {callers : List Activation} {world final : World} {active after : Activation}
    (steps : Calling.Prefix callee callers (headCode 15) ((headActions.drop 8).take 7) world active final after)
    (ha : active.Valid world) (hc : ∀ caller ∈ callers, caller.Valid world) (hw : world.WellFormed)
    (slot : Nat) (member : slot ∈ [27, 28, 29, 30]) : after.state slot = active.state slot := by
  apply steps.observed_local_same ha hc hw
  · intro offset bound
    change offset < 7 at bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> interval_cases offset <;> decide +kernel
  · decide +kernel
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> decide +kernel

end SubtreeProofs.Rust.SourceEval.Evaluator
