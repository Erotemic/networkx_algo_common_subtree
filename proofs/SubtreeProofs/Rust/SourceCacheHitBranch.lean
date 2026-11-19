module

public import SubtreeProofs.Rust.SourceCacheHitPrelude
public import SubtreeProofs.Rust.SourceCacheHitCleanup

/-! The whole pinned cache-hit branch executes from the independently
constructed lookup scope, including movement of the owned table and all branch
cleanup. Input queries may alias table data or suspended caller data. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem LookupScope.root_support {world : World} {active initial : Activation}
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none)
    {slot : Nat} (outside : slot ∉ [0, 1, 2, 3, 4, 6]) : active.roots slot = none := by
  by_cases retired : slot ∈ [5, 7, 8]
  · exact scope.retired slot retired
  · rw [scope.otherRoots slot (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside retired ⊢
      tauto)]
    apply unbound slot
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
    tauto

theorem hit_branch_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 13 ≤ active.count)
    (result : CommonEmbedding) (hit : (LookupEvents.lookup table left right).1 = some result) :
    ∃ final after,
      Calling.Prefix callee callers .done hitActions world active final after ∧
      QueryMachine before callers previous external final after ∧ after.count = active.count ∧
      (∀ slot ∈ [0, 1, 2, 3], after.roots slot = active.roots slot) ∧
      (∀ slot, slot ∉ [0, 1, 2, 3] → after.roots slot = none) ∧
      after.state 0 = Slot.ofValue (encodeOutput (some result) table) ∧ after.state 3 = .empty := by
  obtain ⟨w9, a9, root9, root10, root12, first, m9, count9, other9,
    hb9, hb10, hb11, hb12, raw12, ⟨root0, hb0, raw0⟩, empty0, table3, hole4, empty6, empty9, value10, empty12⟩ :=
    hit_prelude_complete h callee scope unbound count result hit
  obtain ⟨w11, a11, transfer, m11, roots11, count11, output0, empty3, empty10, empty12'⟩ :=
    hit_transfer_complete m9 callee result table hb0 hb12 raw0 raw12 empty0 empty12 table3 value10
  have hole4' : a11.state 4 = .node .optional 1 [.empty] :=
    (transfer.closed_local_same (index := 4) m9.native.valid m9.native.callersValid m9.native.wellFormed
      (by rw [hole4]; exact cached_payload_hole_typed) (.adt .optional) (by decide +kernel) (by decide +kernel)).trans hole4
  have empty6' : a11.state 6 = .empty :=
    (transfer.closed_local_same (index := 6) m9.native.valid m9.native.callersValid m9.native.wellFormed
      (by rw [empty6]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty6
  have empty9' : a11.state 9 = .empty :=
    (transfer.closed_local_same (index := 9) m9.native.valid m9.native.callersValid m9.native.wellFormed
      (by rw [empty9]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty9
  obtain ⟨root4, bound4⟩ := scope.resultRoot
  obtain ⟨root6, pointer, bound6, raw6⟩ := scope.viewRoot
  obtain ⟨final, after, cleanup, machine, rootsAfter, countAfter, outputAfter, emptyAfter⟩ :=
    hit_cleanup_complete m11 callee (by rw [roots11, other9 4 (by decide)]; exact bound4)
      (by rw [roots11, other9 6 (by decide)]; exact bound6)
      (by rw [roots11]; exact hb9) (by rw [roots11]; exact hb10) (by rw [roots11]; exact hb12)
      empty3 hole4' empty6' empty9' empty10 empty12' output0
  have tail : Calling.Prefix callee callers .done (hitActions.drop 9) w9 a9 final after := by
    have joined := transfer.append cleanup
    exact joined
  have whole : Calling.Prefix callee callers .done hitActions world active final after := by
    have joined := first.append tail
    exact joined
  refine ⟨final, after, whole, machine, countAfter.trans (count11.trans count9), ?_, ?_, outputAfter, emptyAfter⟩
  · intro slot member
    rw [rootsAfter, hitCleanupRoots, roots11]
    have outside : slot ∉ [9, 10, 11, 12] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> decide
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> simp only [Roots.set] <;> exact other9 _ outside
  · intro slot outside
    rw [rootsAfter, hitCleanupRoots, roots11]
    by_cases four : slot = 4
    · subst slot; simp only [Roots.set, ite_true]
    by_cases six : slot = 6
    · subst slot; simp only [Roots.set, show (6 : Nat) ≠ 4 by decide, ite_false, ite_true]
    by_cases nine : slot = 9
    · subst slot; simp [Roots.set]
    by_cases ten : slot = 10
    · subst slot; simp [Roots.set]
    by_cases twelve : slot = 12
    · subst slot; simp [Roots.set]
    simp only [Roots.set, four, six, nine, ten, twelve, ite_false]
    by_cases eleven : slot = 11
    · subst slot; exact hb11
    rw [other9 slot (by simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using And.intro nine (And.intro ten (And.intro eleven twelve)))]
    exact scope.root_support unbound (by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢
      tauto)

end SubtreeProofs.Rust.SourceEval.Evaluator
