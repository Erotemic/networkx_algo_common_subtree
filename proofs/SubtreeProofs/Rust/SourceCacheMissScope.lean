module

public import SubtreeProofs.Rust.SourceCacheMissAggregate
public import SubtreeProofs.Rust.SourceCacheHitBranch

/-! All eleven actual miss setup instructions reach the native word cases with
an initialized query tuple, original query-loan origins, owned table and fresh
return storage. The selected empty/recursive branch remains a separate proof. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure MissScope (initial : Activation) (left right : BalancedWord) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  inputs : InputLocals left right table active.state
  count : active.count = initial.count
  tuple : active.state 13 = queryTuple left right
  tupleRoot : ∃ binding, active.roots 13 = some binding
  returnRoot : ∃ binding, active.roots 0 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  returnEmpty : active.state 0 = .empty
  otherRoots : ∀ slot, slot ∉ [0, 13] → active.roots slot = initial.roots slot

theorem miss_setup_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : QueryMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (scope : LookupScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 16 ≤ active.count)
    (miss : (LookupEvents.lookup table left right).1 = none) :
    ∃ final after, Calling.Prefix callee callers missCases missSetupActions world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ MissScope initial left right table final after ∧
      QueryOrigins final after before.memory.length ∧ LoanOrigin final after before.memory.length 13 ∧
      ClosedOutside [1, 2, 13] after.state ∧ WordLoanState after.state := by
  obtain ⟨wr, ar, retire, mr, ir, countR, memoryR, retired4, retired6, otherR, emptyR, ⟨root0, bound0R, raw0R⟩⟩ :=
    miss_retire_complete h callee scope miss
  obtain ⟨root1, bound1⟩ := Activation.root_of_materialize mr.native.valid (value := .reference (encodeWord left))
    (by rw [ir.left]; simp only [Slot.materialize])
  obtain ⟨root2, bound2⟩ := Activation.root_of_materialize mr.native.valid (value := .reference (encodeWord right))
    (by rw [ir.right]; simp only [Slot.materialize])
  have unboundR : ∀ slot ∈ [13, 14, 15], ar.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;>
      rw [otherR _ (by decide) (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨wc, ac, root13, root14, root15, pointer1, pointer2, copies, mc, ic, qc, cc, countC,
    bound13, bound14, bound15, otherC, empty13, value14, value15, raw13, raw14, raw15, raw1, raw2, memoryC⟩ :=
    miss_copies_complete mr callee ir bound1 bound2 (by rw [countR]; exact count) unboundR
  have bound1C : ac.roots 1 = some root1 := by rw [otherC 1 (by decide)]; exact bound1
  have bound2C : ac.roots 2 = some root2 := by rw [otherC 2 (by decide)]; exact bound2
  obtain ⟨final, after, aggregateRun, machine, inputs, queries, tupleOrigin, closed, words, countAfter,
    retired14, retired15, otherAfter, tuple, finalMemory, rawTuple⟩ :=
    miss_aggregate_complete mc callee ic qc cc bound1C bound2C bound13 bound14 bound15 raw13 raw14 raw15 raw1 raw2 empty13 value14 value15
  have tail : Calling.Prefix callee callers missCases (missSetupActions.drop 3) wr ar final after :=
    Calling.Prefix.append (suffix := missCases) (rest := missSetupActions.drop 8) copies aggregateRun
  have whole : Calling.Prefix callee callers missCases missSetupActions world active final after :=
    Calling.Prefix.append (suffix := missCases) (rest := missSetupActions.drop 3) retire tail
  have returnEmpty : after.state 0 = .empty :=
    (whole.closed_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.returnEmpty]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans scope.returnEmpty
  have returnBoundC : ac.roots 0 = some root0 := by rw [otherC 0 (by decide)]; exact bound0R
  have raw0C := memoryC 0 root0 bound0R _ raw0R
  have raw0After : final.memory[root0.address]? = some (.node .tuple 0 []) := by
    rw [finalMemory]
    exact Activation.write_other_root mc.valid bound13 returnBoundC (by decide) raw0C _
  have ownScope : MissScope initial left right table final after := by
    refine ⟨inputs, countAfter.trans (countC.trans (countR.trans scope.count)), tuple,
      ⟨root13, by rw [otherAfter 13 (by decide) (by decide)]; exact bound13⟩,
      ⟨root0, by rw [otherAfter 0 (by decide) (by decide)]; exact returnBoundC, raw0After⟩, returnEmpty, ?_⟩
    intro slot outside
    by_cases fourteen : slot = 14
    · subst slot; rw [retired14]; exact (unbound 14 (by decide)).symm
    by_cases fifteen : slot = 15
    · subst slot; rw [retired15]; exact (unbound 15 (by decide)).symm
    rw [otherAfter slot fourteen fifteen]
    have not13 : slot ≠ 13 := by intro same; subst slot; simp at outside
    rw [otherC slot (by simp [not13, fourteen, fifteen])]
    by_cases four : slot = 4
    · subst slot; rw [retired4]; exact (unbound 4 (by decide)).symm
    by_cases six : slot = 6
    · subst slot; rw [retired6]; exact (unbound 6 (by decide)).symm
    rw [otherR slot four six]
    by_cases temporary : slot ∈ [5, 7, 8]
    · rw [scope.retired slot temporary]
      apply Eq.symm
      apply unbound slot
      simp only [List.mem_cons, List.not_mem_nil, or_false] at temporary
      rcases temporary with rfl | rfl | rfl <;> decide
    · exact scope.otherRoots slot (by
        simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside temporary ⊢
        tauto)
  exact ⟨final, after, whole, machine, ownScope, queries, tupleOrigin, closed, words⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
