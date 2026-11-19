module

public import SubtreeProofs.Rust.SourcePairHeadProgram
import Mathlib.Tactic.IntervalCases

/-! Construct all four actual pair-child views from the original copied query
tuple. Their loans remain below the pre-entry memory bound; the owned table and
all other existing root cells are preserved. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_field_view_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external exceptions : List Nat}
    (h : OriginalLoanMachine before callers previous external exceptions world active) (callee : Derived.Callees) (suffix : Code)
    (member : 13 ∈ exceptions) {destination : Nat} (outside : destination ∉ exceptions)
    {lh lt rh rt : BalancedWord} (tuple : active.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt))
    (side child : Nat) (sideBound : side ∈ [0, 1]) (childBound : child ∈ [0, 1])
    (bound : destination < active.count) (unbound : active.roots destination = none) :
    ∃ final after,
      Calling.Prefix callee callers suffix [.storageLive destination, .assign destination (.address (pairFieldPlace side child))]
        world active final after ∧
      OriginalLoanMachine before callers previous external (destination :: exceptions) final after ∧
      after.roots = active.roots.set destination (some ⟨world.memory.length, world.memory.length⟩) ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      after.state destination = .shared (.boxed (encodeWord (pairChild lh lt rh rt side child))) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  exact original_borrow_view_complete h callee suffix member outside rfl (pair_field_route tuple side child sideBound)
    (pair_field_source tuple side child sideBound childBound) (.owned (NativeData.word _)) bound unbound

theorem pair_head_views_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    {lh lt rh rt : BalancedWord} {table : MemoTable} (scope : MissScope initial (.Pair lh lt) (.Pair rh rt) table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 31 ≤ active.count) :
    ∃ final after,
      Calling.Prefix callee callers (headCode 8) (headActions.take 8) world active final after ∧
      OriginalLoanMachine before callers previous external [30, 29, 28, 27, 1, 2, 13] final after ∧
      after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot ∈ [27, 28, 29, 30], ∃ binding, after.roots slot = some binding) ∧
      (∀ slot, slot ∉ [27, 28, 29, 30] → after.roots slot = active.roots slot) ∧
      after.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) ∧ after.state 3 = Slot.ofValue (encodeTable table) ∧
      after.state 27 = .shared (.boxed (encodeWord lh)) ∧ after.state 28 = .shared (.boxed (encodeWord lt)) ∧
      after.state 29 = .shared (.boxed (encodeWord rh)) ∧ after.state 30 = .shared (.boxed (encodeWord rt)) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  have unbound0 : ∀ slot ∈ [27, 28, 29, 30], active.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rw [scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨w27, a27, run27, m27, roots27, count27, frame27, value27, memory27⟩ :=
    pair_field_view_complete h callee (headCode 2) (by simp) (destination := 27) (by decide) scope.tuple
      0 0 (by simp) (by simp) (by omega) (unbound0 27 (by simp))
  have tuple27 : a27.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) :=
    (run27.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  obtain ⟨w28, a28, run28, m28, roots28, count28, frame28, value28, memory28⟩ :=
    pair_field_view_complete m27 callee (headCode 4) (by simp) (destination := 28) (by decide) tuple27
      0 1 (by simp) (by simp) (by rw [count27]; omega) (by simpa [roots27, Roots.set] using unbound0 28 (by simp))
  have tuple28 : a28.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) :=
    (run28.unshared_local_same (index := 13) m27.native.valid m27.native.callersValid m27.native.wellFormed
      (by rw [tuple27]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple27
  obtain ⟨w29, a29, run29, m29, roots29, count29, frame29, value29, memory29⟩ :=
    pair_field_view_complete m28 callee (headCode 6) (by simp) (destination := 29) (by decide) tuple28
      1 0 (by simp) (by simp) (by rw [count28, count27]; omega)
      (by simpa [roots28, roots27, Roots.set] using unbound0 29 (by simp))
  have tuple29 : a29.state 13 = queryTuple (.Pair lh lt) (.Pair rh rt) :=
    (run29.unshared_local_same (index := 13) m28.native.valid m28.native.callersValid m28.native.wellFormed
      (by rw [tuple28]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple28
  obtain ⟨final, after, run30, machine, roots30, count30, frame30, value30, memory30⟩ :=
    pair_field_view_complete m29 callee (headCode 8) (by simp) (destination := 30) (by decide) tuple29
      1 1 (by simp) (by simp) (by rw [count29, count28, count27]; omega)
      (by simpa [roots29, roots28, roots27, Roots.set] using unbound0 30 (by simp))
  have last4 : Calling.Prefix callee callers (headCode 8) ((headActions.drop 4).take 4) w28 a28 final after :=
    Calling.Prefix.append (suffix := headCode 8) (rest := (headActions.drop 6).take 2) run29 run30
  have last6 : Calling.Prefix callee callers (headCode 8) ((headActions.drop 2).take 6) w27 a27 final after :=
    Calling.Prefix.append (suffix := headCode 8) (rest := (headActions.drop 4).take 4) run28 last4
  have whole : Calling.Prefix callee callers (headCode 8) (headActions.take 8) world active final after :=
    Calling.Prefix.append (suffix := headCode 8) (rest := (headActions.drop 2).take 6) run27 last6
  have same27 := last6.observed_local_same (index := 27) m27.native.valid m27.native.callersValid m27.native.wellFormed
    (by intro offset bound; change offset < 6 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  have same28 := last4.observed_local_same (index := 28) m28.native.valid m28.native.callersValid m28.native.wellFormed
    (by intro offset bound; change offset < 4 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  have same29 := run30.observed_local_same (index := 29) m29.native.valid m29.native.callersValid m29.native.wellFormed
    (by intro offset bound; change offset < 2 at bound; interval_cases offset <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  refine ⟨final, after, whole, machine, count30.trans (count29.trans (count28.trans count27)),
    frame30.trans (frame29.trans (frame28.trans frame27)), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp [roots30, roots29, roots28, roots27, Roots.set]
  · intro slot outside
    have different : slot ≠ 27 ∧ slot ≠ 28 ∧ slot ≠ 29 ∧ slot ≠ 30 := by simpa using outside
    simp only [roots30, roots29, roots28, roots27, Roots.set, different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · exact (whole.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.tuple
  · exact (whole.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.inputs.table]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.inputs.table
  · simpa [pairChild] using same27.trans value27
  · simpa [pairChild] using same28.trans value28
  · simpa [pairChild] using same29.trans value29
  · simpa [pairChild] using value30
  · intro index binding root raw read
    have root27 : a27.roots index = some binding := by
      have other : index ≠ 27 := by intro same; subst index; rw [unbound0 27 (by simp)] at root; cases root
      simpa only [roots27, Roots.set, other, ite_false] using root
    have root28 : a28.roots index = some binding := by
      have other : index ≠ 28 := by intro same; subst index; rw [unbound0 28 (by simp)] at root; cases root
      simpa only [roots28, Roots.set, other, ite_false] using root27
    have root29 : a29.roots index = some binding := by
      have other : index ≠ 29 := by intro same; subst index; rw [unbound0 29 (by simp)] at root; cases root
      simpa only [roots29, Roots.set, other, ite_false] using root28
    exact memory30 index binding root29 raw (memory29 index binding root28 raw (memory28 index binding root27 raw (memory27 index binding root raw read)))

end SubtreeProofs.Rust.SourceEval.Evaluator
