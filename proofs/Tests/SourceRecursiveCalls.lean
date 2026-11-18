module

import SubtreeProofs.Rust.SourceEvalTypedRecursive
import SubtreeProofs.Rust.SourceOwnerRecursive
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceRecursiveCallsTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

-- A caller retains both a scalar and a reference to that same scalar. Its
-- complete read inventory includes an alias occurrence, independently of the
-- two Box owners transferred to the choice invocation.
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], .number 99, .shared ⟨2, []⟩],
  fun a => if a < 2 then some .box else if a = 2 then some (.stack 77 1 2)
    else if a = 3 then some (.stack 77 2 3) else none, fun a => decide (a < 4)⟩
private def caller : Activation := ⟨77, 3,
  fun s => if s = 1 then some ⟨2, 2⟩ else if s = 2 then some ⟨3, 3⟩ else none,
  fun s => if s = 1 then .number 99 else if s = 2 then .shared (.number 99) else .empty⟩
private def guards : List Nat := [2, 3, 2]
private theorem world_wf : world.WellFormed := by
  constructor
  · intro a
    change ((if a < 2 then some Class.box else if a = 2 then some (.stack 77 1 2)
      else if a = 3 then some (.stack 77 2 3) else none).isSome = true ↔ a < 4)
    split_ifs <;> simp_all <;> omega
  · intro a h
    exact of_decide_eq_true h
private theorem caller_valid : caller.Valid world := by
  refine ⟨?_, [2, 3], ?_, ?_⟩
  · intro slot hs
    change 3 ≤ slot at hs
    have h1 : slot ≠ 1 := by omega
    have h2 : slot ≠ 2 := by omega
    simp only [caller, h1, h2, ite_false]
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;> rfl
  · intro slot
    by_cases h1 : slot = 1
    · subst slot
      exact ⟨.number 99, [], rfl, rfl, .number 99, by simp⟩
    · by_cases h2 : slot = 2
      · subst slot
        exact ⟨.shared ⟨2, []⟩, [2], rfl, rfl, .shared (.shared rfl (.number 99)), by simp⟩
      · simp only [caller, h1, h2, ite_false]
private theorem caller_scan : scanCallers world [caller] = some (⟨[2, 2, 3], [], [2]⟩ : Resources) := by with_unfolding_all rfl

private def first : CommonEmbedding := ⟨.Pair .Empty .Empty, 1#u32⟩
private def second : CommonEmbedding := ⟨.Empty, 3#u32⟩
private def packets : List ValueCell := [
  (.node .embedding 0 [.node .word 1 [.owned 0, .owned 1], .number 1], encodeResult first),
  (.node .embedding 0 [.node .word 0 [], .number 3], encodeResult second)]
private theorem readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
  intro p hm
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl
  · exact ⟨[0, 1], .node (.cons (.node (.cons (.owned rfl (.node .nil))
      (.cons (.owned rfl (.node .nil)) .nil))) (.cons (.number _) .nil)), by simp [AliveOn, world]⟩
  · exact ⟨[], .node (.cons (.node .nil) (.cons (.number _) .nil)), by simp [AliveOn]⟩
private theorem guards_alive : AliveOn world.live guards := by
  intro a ha
  simp only [guards, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> rfl

private theorem choice_step (budget fuel : Nat) (w : World) (guarded : List Nat) (stack : List Activation) (args : List ValueCell) :
    Recursive.original budget (fuel + 1) w guarded stack .chooseLonger args =
      Calling.guardedInvoke (Recursive.original budget fuel) stack guarded SourceEval.CallingCertificate.originalChoice w args := by
  simp only [Recursive.original, Recursive.run, Recursive.interpreted, SourceEval.CallingCertificate.choice_lookup,
    ite_true, Bind.bind, Option.bind]

private def choice := Recursive.original 0 1 world guards [caller] .chooseLonger packets
private theorem choice_exists : choice.isSome = true := by
  rw [choice, choice_step]
  obtain ⟨hf, hn, hcode⟩ := SourceEval.CallingCertificate.originalChoice_spec
  simp only [Calling.guardedInvoke, Calling.invoke, hf, hn, hcode]
  decide +kernel

-- Budget zero is sufficient for call-free choice; fuel one executes its entry
-- and full body. Both losing Boxes retire, every callee stack root closes, and
-- the transitive aliased caller graph remains live with its original cells.
example : choice.map (fun (w, _, cost) =>
    ((List.range 10).map w.live, cost.work.steps, cost.destroyed.boxes)) =
      some ([false, false, true, true, false, false, false, false, false, false], 34, 2) := by
  rw [choice, choice_step]
  obtain ⟨hf, hn, hcode⟩ := SourceEval.CallingCertificate.originalChoice_spec
  simp only [Calling.guardedInvoke, Calling.invoke, hf, hn, hcode]
  decide +kernel

example : ∃ final packet cost, choice = some (final, packet, cost) ∧
    packet.2 = encodeResult (OrderedSolver.selectResult first second) ∧ cost = SourceEval.Choice.cost first second ∧
    Preserves world final guards ∧ caller.Valid final := by
  obtain ⟨⟨final, packet, cost⟩, hr⟩ := Option.isSome_iff_exists.mp choice_exists
  obtain ⟨hv, hcost, _, _, kept⟩ := Recursive.original_choice_refines 0 0 world_wf (by simpa using caller_valid)
    readable guards_alive first second rfl hr
  have scan := scanCallers_spec (by simpa using caller_valid) caller_scan
  have retained : Preserves world final [2, 2, 3] := kept.weaken (by simp [guards])
  have finalCallers := scan.transport retained
  obtain ⟨_, current, _, _, _⟩ := finalCallers.get (a := caller) (by simp)
  exact ⟨final, packet, cost, hr, hv, hcost, kept, current.valid⟩

-- The full recursive ownership theorem is consumed on the actual choice
-- run. Its losing owned word is destroyed; aliased caller reads remain allowed.
example : ∃ final packet cost outputOwners, choice = some (final, packet, cost) ∧
    Footprint final.memory packet.1 outputOwners ∧
    OwnerFrame final (outputOwners ++ (callerOwners final [caller] ++ [])) ∧
    BoxCoverage final (outputOwners ++ (callerOwners final [caller] ++ [])) := by
  obtain ⟨⟨final, packet, cost⟩, hr⟩ := Option.isSome_iff_exists.mp choice_exists
  have input : FieldsFootprint world.memory (packets.map Prod.fst) (packetOwners world packets) := packetOwners_footprint readable
  have frame : OwnerFrame world (packetOwners world packets ++ (callerOwners world [caller] ++ [])) := by
    rw [show packetOwners world packets ++ (callerOwners world [caller] ++ []) = [0, 1] by decide +kernel]
    refine ⟨by decide +kernel, ?_, ?_⟩
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl <;> rfl
  have coverage : BoxCoverage world (packetOwners world packets ++ (callerOwners world [caller] ++ [])) := by
    rw [show packetOwners world packets ++ (callerOwners world [caller] ++ []) = [0, 1] by decide +kernel]
    intro a hc _
    change (if a < 2 then some Class.box else _) = some .box at hc
    split_ifs at hc with h <;> simp_all
    omega
  have typed : SnapshotFieldsTyped (packets.map Prod.snd) (SourceEval.Types.inputs .chooseLonger) :=
    .cons (result_typed first) (.cons (result_typed second) .nil)
  have outputType : SourceEval.Types.callOutput .chooseLonger (SourceEval.Types.inputs .chooseLonger) =
      some (SourceEval.Types.output .chooseLonger) := by
    simp only [SourceEval.Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  obtain ⟨owners, hp⟩ := Recursive.original_owns 0 1 world guards [caller] .chooseLonger packets final packet cost
    (packetOwners world packets) [] world_wf (by simpa using caller_valid) readable guards_alive
    ⟨_, _, typed, outputType⟩ input frame coverage hr
  exact ⟨final, packet, cost, owners, hr, hp⟩

example : Recursive.original 0 0 world guards [caller] .chooseLonger packets = none := rfl
example : (Recursive.original 0 1 world [0] [caller] .chooseLonger packets).isNone = true := by
  rw [choice_step]
  decide +kernel
example : (Recursive.original 0 1 (world.retire [2]) guards [caller] .chooseLonger packets).isNone = true := by
  rw [choice_step]
  decide +kernel

-- Native input types discharge every selected call's input condition. Concrete
-- success remains explicit; no complete source/native answer is a premise.
example (budget fuel : Nat) (w final : World) (stack : List Activation) (guarded : List Nat)
    (args : List ValueCell) (packet : ValueCell) (cost : SourceEval.Cost)
    (hw : w.WellFormed) (hc : ∀ a ∈ stack, a.Valid w)
    (hp : ∀ p ∈ args, Readable w.memory w.live p.1 p.2) (hl : AliveOn w.live guarded)
    (left right : BalancedWord) (table : MemoTable)
    (hi : args.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (hr : Recursive.original budget fuel w guarded stack .evaluate args = some (final, packet, cost)) :
    ∃ result output, packet.2 = SourceEval.Evaluator.encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      SourceEval.Evaluator.Evaluation fuel left right table result output cost ∧ Preserves w final guarded := by
  obtain ⟨result, output, hv, hn, he, _, _, kept⟩ :=
    Recursive.original_evaluate_typed_refines budget fuel hw hc hp hl left right table hi hr
  exact ⟨result, output, hv, hn, he, kept⟩

-- Arbitrary native queries/warm tables retain the completed native result,
-- exact Evaluation costs, protected bytes and complete output/caller ownership.
example (budget fuel : Nat) (w final : World) (stack : List Activation) (guarded : List Nat)
    (args : List ValueCell) (packet : ValueCell) (cost : SourceEval.Cost) (owners external : List Nat)
    (hw : w.WellFormed) (hc : ∀ a ∈ stack, a.Valid w)
    (hp : ∀ p ∈ args, Readable w.memory w.live p.1 p.2) (hl : AliveOn w.live guarded)
    (left right : BalancedWord) (table : MemoTable)
    (hi : args.map Prod.snd = [.reference (encodeWord left), .reference (encodeWord right), encodeTable table])
    (ho : FieldsFootprint w.memory (args.map Prod.fst) owners)
    (hf : OwnerFrame w (owners ++ (callerOwners w stack ++ external)))
    (covered : BoxCoverage w (owners ++ (callerOwners w stack ++ external)))
    (hr : Recursive.original budget fuel w guarded stack .evaluate args = some (final, packet, cost)) :
    ∃ result output outputOwners, packet.2 = SourceEval.Evaluator.encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      SourceEval.Evaluator.Evaluation fuel left right table result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves w final guarded ∧
      Footprint final.memory packet.1 outputOwners ∧
      OwnerFrame final (outputOwners ++ (callerOwners final stack ++ external)) ∧
      BoxCoverage final (outputOwners ++ (callerOwners final stack ++ external)) :=
  Recursive.original_evaluate_owned_refines budget fuel hw hc hp hl left right table hi ho hf covered hr

-- Direct instructions retain their strict loan guard. Calling control can end
-- certified unused shared-reference views; that certificate does not remove
-- the primitive guard witnessed here. See SourceLoanEndings for the full block.
private def loanWorld : World := ⟨[.owned 3, .shared ⟨0, []⟩, .node .tuple 0 [], .number 7], fun a =>
  if a = 0 then some (.stack 10 3 0) else if a = 1 then some (.stack 10 6 1)
  else if a = 2 then some (.stack 10 12 2) else if a = 3 then some .box else none,
  fun a => decide (a < 4)⟩
private def loanActive : Activation := ⟨10, 13, fun s =>
  if s = 3 then some ⟨0, 0⟩ else if s = 6 then some ⟨1, 1⟩ else if s = 12 then some ⟨2, 2⟩ else none,
  fun s => if s = 3 then .boxed (.number 7) else if s = 6 then .shared (.boxed (.number 7)) else .empty⟩
example : loanActive.scan loanWorld = some (⟨[3, 0, 3, 0, 1, 2], [3], [3, 0]⟩ : Resources) := by with_unfolding_all rfl
example : Derived.assign loanWorld loanActive [] 12 (.use (.move (.local 3))) = none := by decide +kernel
example (calls : SourceEval.Calls) : SourceEval.action calls loanActive.state (.assign 12 (.use (.move (.local 3)))) =
    some (((loanActive.state.set 3 .empty).set 12 (.boxed (.number 7))), SourceEval.Cost.local 2) := by with_unfolding_all rfl

end SourceRecursiveCallsTests
