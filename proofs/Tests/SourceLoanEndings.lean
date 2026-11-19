module

import SubtreeProofs.Rust.SourceEvalRecursiveRefinement
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceLoanEndingsTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval SourceEval.Addressed

private def world : World := ⟨[.owned 3, .shared ⟨0, []⟩, .node .tuple 0 [], .number 7], fun a =>
  if a = 0 then some (.stack 10 3 0) else if a = 1 then some (.stack 10 6 1)
  else if a = 2 then some (.stack 10 12 2) else if a = 3 then some .box else none,
  fun a => decide (a < 4)⟩
private def active : Activation := ⟨10, 13, fun s =>
  if s = 3 then some ⟨0, 0⟩ else if s = 6 then some ⟨1, 1⟩ else if s = 12 then some ⟨2, 2⟩ else none,
  fun s => if s = 3 then .boxed (.number 7) else if s = 6 then .shared (.boxed (.number 7)) else .empty⟩
private def program : SourceEval.Code :=
  .step (.storageLive 0) (.step (.assign 12 (.use (.move (.local 3))))
    (.step (.assign 0 (.use (.move (.local 12))))
      (.step (.storageDead 6) (.step (.storageDead 12) (.step (.storageDead 3) .ret)))))
private def observed := active.forgetRefs program
private def backend := Recursive.original 0 0

private theorem well_formed : world.WellFormed := by
  constructor
  · intro a
    change ((if a = 0 then some (.stack 10 3 0) else if a = 1 then some (.stack 10 6 1)
      else if a = 2 then some (.stack 10 12 2) else if a = 3 then some Class.box else none).isSome = true ↔ a < 4)
    split_ifs <;> simp_all
    omega
  · intro a ha
    exact of_decide_eq_true ha
private theorem valid : active.Valid world := by
  refine ⟨?_, [0, 1, 2, 3], ?_, ?_⟩
  · intro slot hs
    change 13 ≤ slot at hs
    have h3 : slot ≠ 3 := by omega
    have h6 : slot ≠ 6 := by omega
    have h12 : slot ≠ 12 := by omega
    simp only [active, h3, h6, h12, ite_false]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl <;> rfl
  · intro slot
    by_cases h3 : slot = 3
    · subst slot
      exact ⟨.owned 3, [3], rfl, rfl, .owned rfl (.number 7), by simp⟩
    · by_cases h6 : slot = 6
      · subst slot
        exact ⟨.shared ⟨0, []⟩, [3, 0], rfl, rfl, .shared (.shared rfl (.owned rfl (.number 7))), by simp⟩
      · by_cases h12 : slot = 12
        · subst slot
          exact ⟨.node .tuple 0 [], [], rfl, rfl, .empty _, by simp⟩
        · simp only [active, h3, h6, h12, ite_false]

-- The low-level move guard remains strict. The full block may end this unused
-- reference view because its actual storage-dead marker precedes observation.
example : Derived.assign world active [] 12 (.use (.move (.local 3))) = none := by decide +kernel
example : LoanEnding.endsBeforeObservation 6 program = true := by decide +kernel
example : observed.state 6 = .empty := by with_unfolding_all rfl
example : observed.state 3 = .boxed (.number 7) := by with_unfolding_all rfl
example : observed.roots = active.roots ∧ observed.frame = active.frame ∧ observed.count = active.count := ⟨rfl, rfl, rfl⟩
example : world.memory[1]? = some (.shared ⟨0, []⟩) ∧ world.live 1 = true := ⟨rfl, rfl⟩
example : observed.Valid world := Activation.forgetRefs_valid valid program
example (calls : SourceEval.Calls) : SourceEval.exec calls program observed.state = SourceEval.exec calls program active.state :=
  active.forgetRefs_source program calls

example : (Calling.exec backend [] program world active).map (fun (flow, cost) =>
    ((match flow with | .returned _ _ (_, .boxed (.number n)) => n | _ => 0),
      cost.work.steps, traceResources flow.world.memory (.owned 3) (.boxed (.number 7)), flow.world.live 1)) =
    some (7, 9, some ⟨[3], [3], []⟩, false) := by decide +kernel

example : ∃ flow cost, Calling.exec backend [] program world active = some (flow, cost) ∧
    SourceEval.exec (SourceEval.run SourceEval.Certificate.original.body 0) program active.state = some (flow.snapshot, cost) ∧
    flow.Valid [] := by
  have hs : (Calling.exec backend [] program world active).isSome = true := by decide +kernel
  obtain ⟨⟨flow, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have ready := Calling.readyFor_noCalls backend (Recursive.Ready SourceEval.CallingCertificate.originalProgram.definitions 0 0)
    [] program (by decide +kernel) world active
  have h := Calling.exec_spec (Recursive.original_respects 0 0) valid (by simp) well_formed program ready hr
  exact ⟨flow, cost, hr, h.1, h.2.2.2⟩

-- Observing the reference later keeps its loan active. Drops also observe its
-- initialization mask because their exact source destructor cost must remain.
private def laterUse : SourceEval.Code := .step (.assign 12 (.use (.move (.local 3))))
  (.step (.assign 0 (.use (.copy (.local 6)))) (.step (.storageDead 6) .ret))
private def laterDrop : SourceEval.Code := .step (.assign 12 (.use (.move (.local 3)))) (.step (.drop 6) .ret)
example : LoanEnding.endsBeforeObservation 6 laterUse = false := by decide +kernel
example : LoanEnding.endsBeforeObservation 6 laterDrop = false := by decide +kernel
example : (Calling.exec backend [] laterUse world active).isNone = true := by decide +kernel
example : (Calling.exec backend [] laterDrop world active).isNone = true := by decide +kernel

-- An owning mask is never forgotten, even before an otherwise unread reset.
example : (Calling.exec backend [] (.step (.storageDead 3) .ret) world active).isNone = true := by decide +kernel

private def aliasWorld := world.allocate (.stack 10 7 4) (.shared ⟨1, []⟩)
private def aliasActive : Activation := { active with
  roots := active.roots.set 7 (some ⟨4, 4⟩)
  state := active.state.set 7 (.shared (.reference (.boxed (.number 7)))) }
private def aliasUse : SourceEval.Code := .step (.assign 12 (.use (.move (.local 3))))
  (.step (.storageLive 0) (.step (.assign 0 (.use (.copy (.local 7)))) (.step (.storageDead 6) .ret)))
example : LoanEnding.endsBeforeObservation 6 aliasUse = true := by decide +kernel
example : LoanEnding.endsBeforeObservation 7 aliasUse = false := by decide +kernel
example : ((aliasActive.forgetRefs aliasUse).scan aliasWorld).map Resources.loans = some [3, 0, 1] := by decide +kernel
example : (Calling.exec backend [] aliasUse aliasWorld aliasActive).isNone = true := by decide +kernel

end SourceLoanEndingsTests
