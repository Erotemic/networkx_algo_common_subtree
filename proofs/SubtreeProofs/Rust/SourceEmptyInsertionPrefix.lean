module

public import SubtreeProofs.Rust.SourceEmptyInsertCall

/-! Compose the actual empty-witness construction, table transfer, query and
embedding views, and insertion call. The fixed sufficient helper bounds retain
one native inserted-table scope with the original tuple-loan invariant restored. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure EmptyInsertedScope (initial : Activation) (left right : BalancedWord) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  tuple : active.state 13 = queryTuple left right
  witness : active.state 16 = Slot.ofValue (encodeResult emptyWitness)
  table : active.state 18 = Slot.ofValue (encodeTable (.Entry ⟨left, right, emptyWitness⟩ table))
  empty : ∀ slot ∈ [0, 1, 2, 3, 17, 19, 20, 21, 22, 23], active.state slot = .empty
  returnRoot : ∃ binding, active.roots 0 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  live : ∀ slot ∈ [16, 18, 19, 20, 21, 22, 23], ∃ binding, active.roots slot = some binding
  retired17 : active.roots 17 = none
  otherRoots : ∀ slot, slot ∉ [16, 17, 18, 19, 20, 21, 22, 23] → active.roots slot = initial.roots slot

theorem empty_insertion_prefix_complete {before world : World} {active initial : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [1, 2, 13] world active)
    {left right : BalancedWord} {table : MemoTable} (scope : MissScope initial left right table world active)
    (unbound : ∀ slot, slot ∉ [1, 2, 3] → initial.roots slot = none) (count : 24 ≤ active.count) :
    ∃ minimumFuel minimumBudget final after,
      OriginalLoanMachine before callers previous external [1, 2, 13] final after ∧ EmptyInsertedScope active left right table final after ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Calling.Prefix (Recursive.original budget fuel) callers (emptyCode 19) (emptyActions.take 19) world active final after := by
  let callee := Helpers.callee 0 0
  obtain ⟨ww, aw, root16, witnessRun, mw, iw, countW, bound16W, retired17W, otherW, value16W, tupleW, empty0W, ⟨root0, bound0W, raw0W⟩⟩ :=
    empty_witness_complete h callee scope unbound (by omega)
  have unboundW : ∀ slot ∈ [18, 19, 20, 21, 22, 23], aw.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rw [otherW _ (by decide), scope.otherRoots _ (by decide)] <;> exact unbound _ (by decide)
  obtain ⟨wt, tableActive, root18, root19, transferRun, mt, countT, bound18T, bound19T, otherT, empty18T, raw18T,
    table19T, empty3T, query1T, query2T, tupleT, witnessT, memoryT⟩ :=
    empty_table_transfer_complete mw callee iw tupleW value16W (by rw [countW]; omega) (unboundW 18 (by simp)) (unboundW 19 (by simp))
  have unboundT : ∀ slot ∈ [20, 21, 22, 23], tableActive.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rw [otherT _ (by decide) (by decide)] <;> exact unboundW _ (by simp)
  obtain ⟨wq, aq, root20, root21, queryRun, mq, qq, oq, cq, countQ, bound20Q, bound21Q, otherQ,
    empty1Q, query2Q, view20Q, view21Q, tupleQ, memoryQ⟩ :=
    empty_query_views_complete mt callee left right query1T query2T tupleT (by rw [countT, countW]; omega)
      (unboundT 20 (by simp)) (unboundT 21 (by simp))
  have table19Q : aq.state 19 = Slot.ofValue (encodeTable table) :=
    (queryRun.closed_local_same (index := 19) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [table19T]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans table19T
  have witnessQ : aq.state 16 = Slot.ofValue (encodeResult emptyWitness) :=
    (queryRun.closed_local_same (index := 16) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [witnessT]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans witnessT
  have empty18Q : aq.state 18 = .empty :=
    (queryRun.unshared_local_same (index := 18) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [empty18T]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans empty18T
  have empty3Q : aq.state 3 = .empty :=
    (queryRun.unshared_local_same (index := 3) mt.native.valid mt.native.callersValid mt.native.wellFormed
      (by rw [empty3T]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans empty3T
  have unboundQ : ∀ slot ∈ [22, 23], aq.roots slot = none := by
    intro slot member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> rw [otherQ _ (by decide) (by decide)] <;> exact unboundT _ (by simp)
  obtain ⟨we, ae, root22, root23, embeddingRun, me, oe, ce, data, countE, bound22E, bound23E, otherE,
    empty1E, empty2E, tupleE, view20E, view21E, view22E, view23E, memoryE⟩ :=
    empty_embedding_views_complete mq callee left right cq oq empty1Q query2Q view20Q view21Q tupleQ witnessQ
      (by rw [countQ, countT, countW]; exact count) (unboundQ 22 (by simp)) (unboundQ 23 (by simp))
  have table19E : ae.state 19 = Slot.ofValue (encodeTable table) :=
    (embeddingRun.closed_local_same (index := 19) mq.valid mq.callersValid mq.wellFormed
      (by rw [table19Q]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans table19Q
  have witnessE : ae.state 16 = Slot.ofValue (encodeResult emptyWitness) :=
    (embeddingRun.closed_local_same (index := 16) mq.valid mq.callersValid mq.wellFormed
      (by rw [witnessQ]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans witnessQ
  have empty18E : ae.state 18 = .empty :=
    (embeddingRun.unshared_local_same (index := 18) mq.valid mq.callersValid mq.wellFormed
      (by rw [empty18Q]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans empty18Q
  have empty3E : ae.state 3 = .empty :=
    (embeddingRun.unshared_local_same (index := 3) mq.valid mq.callersValid mq.wellFormed
      (by rw [empty3Q]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans empty3Q
  have bound18Q : aq.roots 18 = some root18 := by rw [otherQ 18 (by decide) (by decide)]; exact bound18T
  have bound18E : ae.roots 18 = some root18 := by rw [otherE 18 (by decide) (by decide)]; exact bound18Q
  have raw18E : we.memory[root18.address]? = some (.node .tuple 0 []) :=
    memoryE 18 root18 bound18Q _ (memoryQ 18 root18 bound18T _ raw18T)
  obtain ⟨minFuel, minBudget, final, after, cost, finalMachine, roots, countAfter, inserted,
    empty1After, empty2After, tupleAfter, emptyAfter, sameAfter, memoryAfter, callRun⟩ :=
    empty_insert_call_complete me data ce left right table tupleE oe empty1E empty2E table19E view20E view21E view22E view23E
      bound18E empty18E raw18E (by rw [countE, countQ, countT, countW]; exact count)
  have first14 : Calling.Prefix callee callers (emptyCode 14) (emptyActions.take 14) world active wq aq := by
    have tail := Calling.Prefix.append (suffix := emptyCode 14) (rest := (emptyActions.drop 10).take 4) transferRun queryRun
    exact Calling.Prefix.append (suffix := emptyCode 14) (rest := (emptyActions.drop 7).take 7) witnessRun tail
  have first18 : Calling.Prefix callee callers (emptyCode 18) (emptyActions.take 18) world active we ae :=
    Calling.Prefix.append (suffix := emptyCode 18) (rest := (emptyActions.drop 14).take 4) first14 embeddingRun
  have empty0E : ae.state 0 = .empty :=
    (first18.unshared_local_same (index := 0) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.returnEmpty]; intro value same; cases same) (by decide +kernel) (by decide +kernel)).trans scope.returnEmpty
  have witnessAfter : after.state 16 = Slot.ofValue (encodeResult emptyWitness) :=
    (sameAfter 16 (by decide) (LoanEnding.forget_closed (emptyCode 18) _ (by rw [witnessE]; exact ofValue_typed (result_typed emptyWitness)) (.adt .embedding))).trans witnessE
  have empty0After : after.state 0 = .empty := (sameAfter 0 (by decide) ((LoanEnding.forget_empty _ _ empty0E).trans empty0E.symm)).trans empty0E
  have empty3After : after.state 3 = .empty := (sameAfter 3 (by decide) ((LoanEnding.forget_empty _ _ empty3E).trans empty3E.symm)).trans empty3E
  have bound0T : tableActive.roots 0 = some root0 := by rw [otherT 0 (by decide) (by decide)]; exact bound0W
  have bound0Q : aq.roots 0 = some root0 := by rw [otherQ 0 (by decide) (by decide)]; exact bound0T
  have bound0E : ae.roots 0 = some root0 := by rw [otherE 0 (by decide) (by decide)]; exact bound0Q
  have raw0After : final.memory[root0.address]? = some (.node .tuple 0 []) :=
    memoryAfter 0 root0 (by decide) bound0E _ (memoryE 0 root0 bound0Q _ (memoryQ 0 root0 bound0T _ (memoryT 0 root0 bound0W _ raw0W)))
  have root17After : after.roots 17 = none := by
    rw [roots, otherE 17 (by decide) (by decide), otherQ 17 (by decide) (by decide), otherT 17 (by decide) (by decide)]
    exact retired17W
  have empty17After : after.state 17 = .empty := by
    obtain ⟨_, frame⟩ := finalMachine.native.valid.2
    simpa only [root17After] using frame.slots 17
  have finalScope : EmptyInsertedScope active left right table final after := by
    refine ⟨countAfter.trans (countE.trans (countQ.trans (countT.trans countW))), tupleAfter, witnessAfter, inserted, ?_,
      ⟨root0, by rw [roots]; exact bound0E, raw0After⟩, ?_, root17After, ?_⟩
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rest
      · exact empty0After
      · exact empty1After
      · exact empty2After
      · exact empty3After
      · exact empty17After
      · exact emptyAfter slot (by simpa only [List.mem_cons, List.not_mem_nil, or_false] using rest)
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      · exact ⟨root16, by rw [roots, otherE 16 (by decide) (by decide), otherQ 16 (by decide) (by decide), otherT 16 (by decide) (by decide)]; exact bound16W⟩
      · exact ⟨root18, by rw [roots]; exact bound18E⟩
      · exact ⟨root19, by rw [roots, otherE 19 (by decide) (by decide), otherQ 19 (by decide) (by decide)]; exact bound19T⟩
      · exact ⟨root20, by rw [roots, otherE 20 (by decide) (by decide)]; exact bound20Q⟩
      · exact ⟨root21, by rw [roots, otherE 21 (by decide) (by decide)]; exact bound21Q⟩
      · exact ⟨root22, by rw [roots]; exact bound22E⟩
      · exact ⟨root23, by rw [roots]; exact bound23E⟩
    · intro slot outside
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside
      obtain ⟨sixteen, seventeen, eighteen, nineteen, twenty, twentyOne, twentyTwo, twentyThree⟩ := outside
      rw [roots, otherE slot twentyTwo twentyThree, otherQ slot twenty twentyOne, otherT slot eighteen nineteen,
        otherW slot (by simp [sixteen, seventeen])]
  refine ⟨minFuel, minBudget, final, after, finalMachine, finalScope, ?_⟩
  intro fuel budget fuelBound budgetBound
  have beforeCall := first18.noncall_callee (Recursive.original budget fuel) (by decide +kernel)
  exact Calling.Prefix.append (suffix := emptyCode 19) (rest := [.call .insert emptyInsertArgs 18]) beforeCall
    (callRun fuel budget fuelBound budgetBound).2

end SubtreeProofs.Rust.SourceEval.Evaluator
