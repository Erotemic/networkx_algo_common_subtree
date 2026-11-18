module

public import SubtreeProofs.Rust.SourceCacheMissCopies
public import SubtreeProofs.Rust.SourceTupleLoanOrigins
public import SubtreeProofs.Rust.SourceWordLoanPermissions

/-! Construct the real aggregate of the two copied query pointers and retire
both temporary reference roots. The resulting tuple retains only original
query loans, below the caller's pre-entry memory bound. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem miss_aggregate_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : LoanSafeMachine before callers previous external world active) (callee : Derived.Callees)
    {left right : BalancedWord} {table : MemoTable} (inputs : InputLocals left right table active.state)
    (queries : QueryOrigins world active before.memory.length) (closed : ClosedOutside [1, 2, 13, 14, 15] active.state)
    {root1 root2 root13 root14 root15 : Binding} {pointer1 pointer2 : Pointer}
    (bound1 : active.roots 1 = some root1) (bound2 : active.roots 2 = some root2)
    (bound13 : active.roots 13 = some root13) (bound14 : active.roots 14 = some root14) (bound15 : active.roots 15 = some root15)
    (raw13 : world.memory[root13.address]? = some (.node .tuple 0 []))
    (raw14 : world.memory[root14.address]? = some (.shared pointer1)) (raw15 : world.memory[root15.address]? = some (.shared pointer2))
    (raw1 : world.memory[root1.address]? = some (.shared pointer1)) (raw2 : world.memory[root2.address]? = some (.shared pointer2))
    (empty13 : active.state 13 = .empty)
    (value14 : active.state 14 = .shared (encodeWord left)) (value15 : active.state 15 = .shared (encodeWord right)) :
    ∃ final after,
      Calling.Prefix callee callers missCases (missSetupActions.drop 8) world active final after ∧
      LoanSafeMachine before callers previous external final after ∧ InputLocals left right table after.state ∧
      QueryOrigins final after before.memory.length ∧ LoanOrigin final after before.memory.length 13 ∧
      ClosedOutside [1, 2, 13] after.state ∧ WordLoanState after.state ∧
      after.count = active.count ∧ after.roots 14 = none ∧ after.roots 15 = none ∧
      (∀ slot, slot ≠ 14 → slot ≠ 15 → after.roots slot = active.roots slot) ∧
      after.state 13 = queryTuple left right ∧
      final.memory = (world.write root13.address (.node .tuple 0 [.shared pointer1, .shared pointer2])).memory ∧
      final.memory[root13.address]? = some (.node .tuple 0 [.shared pointer1, .shared pointer2]) := by
  let p8 := active.forgetRefs (missCode 8)
  have m8 := h.prepare (missCode 8)
  have i8 := inputs.prepare_miss 8 (by decide)
  have v14 : p8.state 14 = .shared (encodeWord left) :=
    (Activation.forgetRefs_observed active _ 14 (by decide +kernel)).trans value14
  have v15 : p8.state 15 = .shared (encodeWord right) :=
    (Activation.forgetRefs_observed active _ 15 (by decide +kernel)).trans value15
  have empty : ((p8.state.set 14 .empty).set 15 .empty) 13 = .empty := by
    simp only [Partial.Locals.set, show (13 : Nat) ≠ 15 by decide, show (13 : Nat) ≠ 14 by decide, ite_false]
    exact LoanEnding.forget_empty _ _ empty13
  have expression : ∀ current suspended, Scanned world p8 current → Callers world callers suspended →
      Addressed.expression world p8.roots (current.loans ++ suspended.reads) p8.state
        (.aggregate .tuple 0 [.move (.local 14), .move (.local 15)]) =
        some ((.node .tuple 0 [.shared pointer1, .shared pointer2],
          .node .tuple 0 [.reference (encodeWord left), .reference (encodeWord right)]),
          (p8.state.set 14 .empty).set 15 .empty) := by
    intro current suspended scanned callerView
    have allowed14 := m8.move_reference scanned callerView bound14 v14
    have allowed15 := m8.move_reference scanned callerView bound15 v15
    have location14 : Storage.locate world p8.roots (.local 14) = some (.shared pointer1, ⟨root14.address, []⟩) := by
      change Storage.locate world active.roots (.local 14) = _
      simp only [Storage.locate, splitPlace, bound14, raw14, locatePath, bind, Option.bind]
    have location15 : Storage.locate world p8.roots (.local 15) = some (.shared pointer2, ⟨root15.address, []⟩) := by
      change Storage.locate world active.roots (.local 15) = _
      simp only [Storage.locate, splitPlace, bound15, raw15, locatePath, bind, Option.bind]
    exact aggregate_two_packets (active := p8) bound14 bound15 raw14 raw15
      (by rw [v14]; simp only [Slot.materialize]) (by rw [v15]; simp only [Slot.materialize]) (by decide)
      (allowed14 _ _ location14) (allowed15 _ _ location15) .tuple 0
  obtain ⟨assigned, assignedMachine⟩ := m8.assign_packet_empty bound13 raw13 expression empty ((m8.safe.clear 14).clear 15)
    (by simpa only [Slot.ofValue, ofFields, queryTuple] using (queryTuple_words left right).safe)
  simp only [Slot.ofValue, ofFields] at assigned assignedMachine
  let wa := world.write root13.address (.node .tuple 0 [.shared pointer1, .shared pointer2])
  let aa : Activation := {p8 with state := ((p8.state.set 14 .empty).set 15 .empty).set 13 (queryTuple left right)}
  change LoanSafeMachine before callers previous external wa aa at assignedMachine
  have ia : InputLocals left right table aa.state := ((i8.set 14 .empty (by decide)).set 15 .empty (by decide)).set 13 _ (by decide)
  have qa : QueryOrigins wa aa before.memory.length := by
    have retained := (queries.prepare (missCode 8)).write_other m8.valid i8.references bound13 (by decide) (m8.fresh 13 root13 bound13)
      (.node .tuple 0 [.shared pointer1, .shared pointer2])
    exact ((retained.set_other 14 (by decide) .empty).set_other 15 (by decide) .empty).set_other 13 (by decide) _
  have rawa14 := Activation.write_other_root m8.valid bound13 bound14 (by decide) raw14 (.node .tuple 0 [.shared pointer1, .shared pointer2])
  have rawa15 := Activation.write_other_root m8.valid bound13 bound15 (by decide) raw15 (.node .tuple 0 [.shared pointer1, .shared pointer2])
  have rawa1 := Activation.write_other_root m8.valid bound13 bound1 (by decide) raw1 (.node .tuple 0 [.shared pointer1, .shared pointer2])
  have rawa2 := Activation.write_other_root m8.valid bound13 bound2 (by decide) raw2 (.node .tuple 0 [.shared pointer1, .shared pointer2])
  let p9 := aa.forgetRefs (missCode 9)
  have m9 := assignedMachine.prepare (missCode 9)
  have i9 := ia.prepare_miss 9 (by decide)
  have empty15 : p9.state 15 = .empty := by
    apply LoanEnding.forget_empty
    simp only [aa, Partial.Locals.set, show (15 : Nat) ≠ 13 by decide, ite_false, ite_true]
  obtain ⟨end15, md15⟩ := m9.storageDead_reference bound15 rawa15 (by rw [empty15]; decide +kernel)
  let w15 := wa.retire [root15.address]
  let a15 : Activation := {p9 with roots := p9.roots.set 15 none, state := p9.state.set 15 .empty}
  change LoanSafeMachine before callers previous external w15 a15 at md15
  have i15 : InputLocals left right table a15.state := i9.set 15 .empty (by decide)
  have q15 : QueryOrigins w15 a15 before.memory.length :=
    (qa.prepare (missCode 9)).retire_other m9.valid i9.references bound15 (by decide) (m9.fresh 15 root15 bound15)
  let p10 := a15.forgetRefs (missCode 10)
  have m10 := md15.prepare (missCode 10)
  have i10 := i15.prepare_miss 10 (by decide)
  have b14 : p10.roots 14 = some root14 := by
    simpa [p10, a15, p9, aa, p8, Roots.set, Activation.forgetRefs] using bound14
  have empty14 : p10.state 14 = .empty := by
    apply LoanEnding.forget_empty
    simp only [a15, Partial.Locals.set, show (14 : Nat) ≠ 15 by decide, ite_false]
    apply LoanEnding.forget_empty
    simp only [aa, Partial.Locals.set, show (14 : Nat) ≠ 13 by decide, show (14 : Nat) ≠ 15 by decide, ite_false, ite_true]
  obtain ⟨end14, finalMachine⟩ := m10.storageDead_reference b14 rawa14 (by rw [empty14]; decide +kernel)
  let final := w15.retire [root14.address]
  let after : Activation := {p10 with roots := p10.roots.set 14 none, state := p10.state.set 14 .empty}
  change LoanSafeMachine before callers previous external final after at finalMachine
  have finalInputs : InputLocals left right table after.state := i10.set 14 .empty (by decide)
  have finalQueries : QueryOrigins final after before.memory.length :=
    (q15.prepare (missCode 10)).retire_other m10.valid i10.references b14 (by decide) (m10.fresh 14 root14 b14)
  have tupleAtA : aa.state 13 = queryTuple left right := by simp only [aa, Partial.Locals.set, ite_true]
  have tupleAt9 : p9.state 13 = queryTuple left right :=
    (LoanEnding.forget_unshared _ _ (by rw [tupleAtA]; intro value same; cases same)).trans tupleAtA
  have tupleAt15 : a15.state 13 = queryTuple left right := by
    simpa only [a15, Partial.Locals.set, show (13 : Nat) ≠ 15 by decide, ite_false] using tupleAt9
  have tupleAt10 : p10.state 13 = queryTuple left right :=
    (LoanEnding.forget_unshared _ _ (by rw [tupleAt15]; intro value same; cases same)).trans tupleAt15
  have tupleAfter : after.state 13 = queryTuple left right := by
    simpa only [after, Partial.Locals.set, show (13 : Nat) ≠ 14 by decide, ite_false] using tupleAt10
  have root1After : after.roots 1 = some root1 := by simpa [after, p10, a15, p9, aa, p8, Roots.set, Activation.forgetRefs] using bound1
  have root2After : after.roots 2 = some root2 := by simpa [after, p10, a15, p9, aa, p8, Roots.set, Activation.forgetRefs] using bound2
  have root13After : after.roots 13 = some root13 := by simpa [after, p10, a15, p9, aa, p8, Roots.set, Activation.forgetRefs] using bound13
  have raw13After : final.memory[root13.address]? = some (.node .tuple 0 [.shared pointer1, .shared pointer2]) :=
    (world.write_spec ((List.getElem?_eq_some_iff.mp raw13).choose) _).1
  have tupleOrigin : LoanOrigin final after before.memory.length 13 :=
    LoanOrigin.tuple_shared finalMachine.valid root13After root1After root2After raw13After rawa1 rawa2 tupleAfter
      finalInputs.left finalInputs.right (finalQueries 1 (by simp)) (finalQueries 2 (by simp))
  have wide : ClosedOutside [1, 2, 13, 14, 15] after.state :=
    (((((closed.forget (missCode 8) _).clear 14).clear 15).set_exception (by simp) (queryTuple left right)).forget (missCode 9) _ |>.clear 15 |>.forget (missCode 10) _).clear 14
  have finalClosed : ClosedOutside [1, 2, 13] after.state := by
    intro slot outside
    by_cases fourteen : slot = 14
    · subst slot
      exact ⟨.u32, by simp only [after, Partial.Locals.set, ite_true]; exact .empty _, .u32⟩
    by_cases fifteen : slot = 15
    · subst slot
      exact ⟨.u32, by
        change SlotTyped ((p10.state.set 14 .empty) 15) .u32
        simp only [Partial.Locals.set, show (15 : Nat) ≠ 14 by decide, ite_false]
        have cleared : p10.state 15 = .empty := LoanEnding.forget_empty (missCode 10) _
          (show a15.state 15 = .empty by simp only [a15, Partial.Locals.set, ite_true])
        rw [cleared]
        exact .empty _, .u32⟩
    exact wide slot (by simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at outside ⊢; tauto)
  have wordState : WordLoanState after.state := by
    intro slot
    by_cases query : slot ∈ [1, 2, 13]
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at query
      rcases query with rfl | rfl | rfl
      · rw [finalInputs.left]; exact .shared left
      · rw [finalInputs.right]; exact .shared right
      · rw [tupleAfter]; exact queryTuple_words left right
    · obtain ⟨ty, typed, closedType⟩ := finalClosed slot query
      exact WordLoans.of_closed typed closedType
  refine ⟨final, after,
    .cons (Calling.instruction_noncall_run (act := .assign 13 (.aggregate .tuple 0 [.move (.local 14), .move (.local 15)])) assigned)
      (.cons (Calling.instruction_noncall_run (act := .storageDead 15) end15)
        (.cons (Calling.instruction_noncall_run (act := .storageDead 14) end14) (.nil _ _))),
    finalMachine, finalInputs, finalQueries, tupleOrigin, finalClosed, wordState, rfl, ?_, ?_, ?_, tupleAfter, rfl, raw13After⟩
  · simp only [after, Roots.set, ite_true]
  · simp [after, p10, a15, Roots.set, Activation.forgetRefs]
  · intro slot fourteen fifteen
    simp only [after, p10, a15, p9, aa, p8, Activation.forgetRefs, Roots.set, fourteen, fifteen, ite_false]

end SubtreeProofs.Rust.SourceEval.Evaluator
