module

public import SubtreeProofs.Rust.SourceCacheMissRetirement
public import SubtreeProofs.Rust.SourceReferenceCopy

/-! Construct the five actual miss setup instructions that open query-tuple
storage and copy both query references. The exact source pointers and original
loan origins are retained for the subsequent aggregate and table moves. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem miss_copies_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (inputs : InputLocals left right table active.state)
    {root1 root2 : Binding} (bound1 : active.roots 1 = some root1) (bound2 : active.roots 2 = some root2)
    (count : 16 ≤ active.count) (unbound : ∀ slot ∈ [13, 14, 15], active.roots slot = none) :
    ∃ (final : World) (after : Activation) (root13 root14 root15 : Binding) (pointer1 pointer2 : Pointer),
      Calling.Prefix callee callers (missCode 8) ((missSetupActions.drop 3).take 5) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      QueryOrigins final after before.memory.length ∧ ClosedOutside [1, 2, 13, 14, 15] after.state ∧
      after.count = active.count ∧ after.roots 13 = some root13 ∧ after.roots 14 = some root14 ∧ after.roots 15 = some root15 ∧
      (∀ slot, slot ∉ [13, 14, 15] → after.roots slot = active.roots slot) ∧
      after.state 13 = .empty ∧ after.state 14 = .shared (encodeWord left) ∧ after.state 15 = .shared (encodeWord right) ∧
      final.memory[root13.address]? = some (.node .tuple 0 []) ∧
      final.memory[root14.address]? = some (.shared pointer1) ∧ final.memory[root15.address]? = some (.shared pointer2) ∧
      final.memory[root1.address]? = some (.shared pointer1) ∧ final.memory[root2.address]? = some (.shared pointer2) ∧
      (∀ slot binding, active.roots slot = some binding → ∀ cell,
        world.memory[binding.address]? = some cell → final.memory[binding.address]? = some cell) := by
  let p3 := active.forgetRefs (missCode 3)
  have m3 := h.prepare (missCode 3)
  have i3 := inputs.prepare_miss 3 (by decide)
  let root13 : Binding := ⟨world.memory.length, world.memory.length⟩
  let w13 := world.allocate (.stack p3.frame 13 world.memory.length) (.node .tuple 0 [])
  let a13 : Activation := {p3 with roots := p3.roots.set 13 (some root13), state := p3.state.set 13 .empty}
  obtain ⟨live13, m13⟩ := m3.storageLive (slot := 13) (by change 13 < active.count; omega) (unbound 13 (by simp)) (by decide)
  change QueryMachine before callers previous external w13 a13 at m13
  have i13 : InputLocals left right table a13.state := i3.set 13 .empty (by decide)
  have b1 : a13.roots 1 = some root1 := by simpa only [a13, p3, Activation.forgetRefs, Roots.set, show (1 : Nat) ≠ 13 by decide, ite_false] using bound1
  obtain ⟨w14, a14, pointer1, copy14, m14, roots14, count14, value14, raw14, raw1, kept14, memory14, closed14, origins14⟩ :=
    copy_reference_complete m13.native callee (missCode 6) b1 i13.left (NativeData.word left)
      (destination := 14) (by change 14 < active.count; omega)
      (by simpa [a13, p3, Roots.set, Activation.forgetRefs] using unbound 14 (by simp))
  let root14 : Binding := ⟨w13.memory.length, w13.memory.length⟩
  have hb13at14 : a14.roots 13 = some root13 := by simp [roots14, a13, Roots.set]
  have hb14 : a14.roots 14 = some root14 := by simp [roots14, root14, Roots.set]
  have queries14 := origins14 m13.references m13.origins (by decide)
  have left14 : a14.state 1 = .shared (encodeWord left) :=
    (kept14 1 (by decide) (miss_observes_queries 4 (by decide) 1 (by simp))
      (miss_observes_queries 5 (by decide) 1 (by simp))).trans i13.left
  have right14 : a14.state 2 = .shared (encodeWord right) :=
    (kept14 2 (by decide) (miss_observes_queries 4 (by decide) 2 (by simp))
      (miss_observes_queries 5 (by decide) 2 (by simp))).trans i13.right
  have b2 : a14.roots 2 = some root2 := by
    simpa [roots14, a13, p3, Roots.set, Activation.forgetRefs] using bound2
  obtain ⟨final, after, pointer2, copy15, finalMachine, finalRoots, finalCount, value15, raw15, raw2, kept15, memory15, closed15, origins15⟩ :=
    copy_reference_complete m14 callee (missCode 8) b2 right14 (NativeData.word right)
      (destination := 15) (by rw [count14]; change 15 < active.count; omega)
      (by simpa [roots14, a13, p3, Roots.set, Activation.forgetRefs] using unbound 15 (by simp))
  let root15 : Binding := ⟨w14.memory.length, w14.memory.length⟩
  have pair : Calling.Prefix callee callers (missCode 8)
      [.storageLive 14, .assign 14 (.use (.copy (.local 1))), .storageLive 15, .assign 15 (.use (.copy (.local 2)))] w13 a13 final after :=
    Calling.Prefix.append (suffix := missCode 8) (rest := [.storageLive 15, .assign 15 (.use (.copy (.local 2)))]) copy14 copy15
  have whole : Calling.Prefix callee callers (missCode 8) ((missSetupActions.drop 3).take 5) world active final after :=
    .cons (Calling.instruction_noncall_run (act := .storageLive 13) live13) pair
  have first13 : a13.state 13 = .empty := by simp only [a13, Partial.Locals.set, ite_true]
  have tail13 : Calling.Prefix callee callers (missCode 8) ((missSetupActions.drop 4).take 4) w13 a13 final after := pair
  have firstClosed : ClosedOutside [1, 2, 13, 14, 15] a13.state :=
    m13.closed.enlarge (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  have middleClosed : ClosedOutside [1, 2, 13, 14, 15] a14.state :=
    (closed14 _ firstClosed).enlarge (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  have finalClosed : ClosedOutside [1, 2, 13, 14, 15] after.state :=
    (closed15 _ middleClosed).enlarge (by intro slot member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  have refs14 : ReferenceQueries a14.state := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, left14⟩
    · exact Or.inr ⟨_, right14⟩
  have finalLeft : after.state 1 = .shared (encodeWord left) :=
    (kept15 1 (by decide) (miss_observes_queries 6 (by decide) 1 (by simp))
      (miss_observes_queries 7 (by decide) 1 (by simp))).trans left14
  have finalRight : after.state 2 = .shared (encodeWord right) :=
    (kept15 2 (by decide) (miss_observes_queries 6 (by decide) 2 (by simp))
      (miss_observes_queries 7 (by decide) 2 (by simp))).trans right14
  have finalTable : after.state 3 = Slot.ofValue (encodeTable table) :=
    (whole.closed_local_same (index := 3) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [inputs.table]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans inputs.table
  refine ⟨final, after, root13, root14, root15, pointer1, pointer2, whole, finalMachine,
    ⟨finalLeft, finalRight, finalTable⟩, origins15 refs14 queries14 (by decide), finalClosed, finalCount.trans count14, ?_, ?_, ?_, ?_, ?_, ?_, value15,
    ?_, ?_, raw15, ?_, raw2, ?_⟩
  · simp [finalRoots, roots14, a13, Roots.set]
  · simp [finalRoots, hb14, root14, Roots.set]
  · simp [finalRoots, root15, Roots.set]
  · intro slot outside
    have thirteen : slot ≠ 13 := by intro same; subst slot; simp at outside
    have fourteen : slot ≠ 14 := by intro same; subst slot; simp at outside
    have fifteen : slot ≠ 15 := by intro same; subst slot; simp at outside
    simp only [finalRoots, roots14, a13, p3, Activation.forgetRefs, Roots.set, thirteen, fourteen, fifteen, ite_false]
  · exact (tail13.closed_local_same (index := 13) m13.native.valid m13.native.callersValid m13.native.wellFormed
      (by rw [first13]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans first13
  · exact (kept15 14 (by decide) (by decide +kernel) (by decide +kernel)).trans value14
  · exact memory15 13 _ hb13at14 _ (memory14 13 _ (by simp [a13, Roots.set]) _ (world.allocate_spec _ _).2.1)
  · exact memory15 14 _ hb14 _ raw14
  · exact memory15 1 root1 (by simpa [roots14, a13, p3, Roots.set, Activation.forgetRefs] using bound1) _ raw1
  · intro slot binding bound raw read
    have outside13 : slot ≠ 13 := by intro same; subst slot; rw [unbound 13 (by simp)] at bound; cases bound
    have outside14 : slot ≠ 14 := by intro same; subst slot; rw [unbound 14 (by simp)] at bound; cases bound
    have b13 : a13.roots slot = some binding := by simpa only [a13, p3, Activation.forgetRefs, Roots.set, outside13, ite_false] using bound
    have b14 : a14.roots slot = some binding := by simpa only [roots14, Roots.set, outside14, ite_false] using b13
    exact memory15 slot binding b14 raw (memory14 slot binding b13 raw ((world.allocate_keeps h.native.wellFormed _ _ []).memory _ _ read))

end SubtreeProofs.Rust.SourceEval.Evaluator
