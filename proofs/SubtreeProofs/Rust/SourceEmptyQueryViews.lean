module

public import SubtreeProofs.Rust.SourceEmptyTableTransfer
public import SubtreeProofs.Rust.SourcePrefixClosedOutside
import Mathlib.Tactic.IntervalCases

/-! Construct both actual insertion query views. Their raw shared inputs may
alias each other or table-owned data; original tuple loan origins and all
untouched closed locals survive the two view pairs. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem empty_observes_right (index : Nat) (bound : index ≤ 13) :
    LoanEnding.endsBeforeObservation 2 (emptyCode index) = false := by
  interval_cases index <;> decide +kernel

theorem empty_query_views_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active) (callee : Derived.Callees)
    (left right : BalancedWord) (query1 : active.state 1 = .shared (encodeWord left)) (query2 : active.state 2 = .shared (encodeWord right))
    (tuple : active.state 13 = queryTuple left right) (count : 22 ≤ active.count)
    (unbound20 : active.roots 20 = none) (unbound21 : active.roots 21 = none) :
    ∃ (final : World) (after : Activation) (root20 root21 : Binding),
      Calling.Prefix callee callers (emptyCode 14) ((emptyActions.drop 10).take 4) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧
      QueryOrigins final after before.memory.length ∧ LoanOrigin final after before.memory.length 13 ∧
      ClosedOutside [1, 2, 13, 20, 21] after.state ∧ after.count = active.count ∧
      after.roots 20 = some root20 ∧ after.roots 21 = some root21 ∧
      (∀ slot, slot ≠ 20 → slot ≠ 21 → after.roots slot = active.roots slot) ∧
      after.state 1 = .empty ∧ after.state 2 = .shared (encodeWord right) ∧
      after.state 20 = .shared (encodeWord left) ∧ after.state 21 = .shared (encodeWord right) ∧
      after.state 13 = queryTuple left right ∧
      (∀ slot binding, active.roots slot = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w20, a20, first, m20, roots20, count20, value20, kept20, empty20, memory20, ended20, queries20, origins20⟩ :=
    query_view_complete h.native callee (emptyCode 12) 20 1 left query1 (by omega) unbound20
  let root20 : Binding := ⟨world.memory.length, world.memory.length⟩
  have query1at20 : a20.state 1 = .shared (encodeWord left) :=
    (kept20 1 (by decide) (empty_observes_queries 10 (by decide) 1 (by simp)) (by decide +kernel)).trans query1
  have query2at20 : a20.state 2 = .shared (encodeWord right) :=
    (kept20 2 (by decide) (empty_observes_right 10 (by decide)) (empty_observes_right 11 (by decide))).trans query2
  have tuple20 : a20.state 13 = queryTuple left right :=
    (first.unshared_local_same (index := 13) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tuple]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple
  have refs : ReferenceQueries active.state := by
    intro index member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, query1⟩
    · exact Or.inr ⟨_, query2⟩
  have originalQueries : QueryOrigins world active before.memory.length := fun index member => h.origins index (by simpa using List.mem_append_left [13] member)
  have q20 := queries20 refs originalQueries (by decide)
  have originalTuple : LoanOrigin world active before.memory.length 13 := h.origins 13 (by simp)
  have t20 := origins20 13 (by decide) (h.zero 13 (by simp)) originalTuple
  obtain ⟨final, after, second, finalMachine, finalRoots, finalCount, value21, kept21, empty21, memory21, ended21, queries21, origins21⟩ :=
    query_view_complete m20 callee (emptyCode 14) 21 2 right query2at20 (by rw [count20]; omega)
      (by simpa [roots20, Roots.set] using unbound21)
  let root21 : Binding := ⟨w20.memory.length, w20.memory.length⟩
  have whole : Calling.Prefix callee callers (emptyCode 14) ((emptyActions.drop 10).take 4) world active final after :=
    Calling.Prefix.append (suffix := emptyCode 14) (rest := [.storageLive 21, .assign 21 (.address (.deref (.local 2)))]) first second
  have tupleAfter : after.state 13 = queryTuple left right :=
    (second.unshared_local_same (index := 13) m20.valid m20.callersValid m20.wellFormed
      (by rw [tuple20]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans tuple20
  have refs20 : ReferenceQueries a20.state := by
    intro index member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl
    · exact Or.inr ⟨_, query1at20⟩
    · exact Or.inr ⟨_, query2at20⟩
  have finalQueries := queries21 refs20 q20 (by decide)
  have finalTuple := origins21 13 (by decide)
    (by rw [tuple20]; simp [queryTuple, Slot.dropWork, dropFields, DropWork.plus]) t20
  have initialClosed : ClosedOutside [1, 2, 13, 20, 21] active.state :=
    h.closed.enlarge (by intro index member; simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢; tauto)
  have closed20 := first.open_view_closed h.native.valid h.native.callersValid h.native.wellFormed initialClosed (by simp)
  have closedAfter := second.open_view_closed m20.valid m20.callersValid m20.wellFormed closed20 (by simp)
  refine ⟨final, after, root20, root21, whole, finalMachine, finalQueries, finalTuple, closedAfter,
    finalCount.trans count20, ?_, ?_, ?_, ?_, ?_, ?_, value21, tupleAfter, ?_⟩
  · simp [finalRoots, roots20, root20, Roots.set]
  · simp [finalRoots, root21, Roots.set]
  · intro slot twenty twentyOne
    simp only [finalRoots, roots20, Roots.set, twenty, twentyOne, ite_false]
  · exact ended21 1 _ (by decide) (by rw [count20]; omega) query1at20 (by decide +kernel)
  · exact (kept21 2 (by decide) (empty_observes_right 12 (by decide)) (empty_observes_right 13 (by decide))).trans query2at20
  · exact (kept21 20 (by decide) (by decide +kernel) (by decide +kernel)).trans value20
  · intro slot binding root raw memory
    have twenty : slot ≠ 20 := by intro same; subst slot; rw [unbound20] at root; cases root
    have rootAt20 : a20.roots slot = some binding := by simpa only [roots20, Roots.set, twenty, ite_false] using root
    exact memory21 slot binding rootAt20 raw (memory20 slot binding root raw memory)

end SubtreeProofs.Rust.SourceEval.Evaluator
