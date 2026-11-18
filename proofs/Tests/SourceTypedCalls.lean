module

import SubtreeProofs.Rust.SourceEvalTypedRecursive
import SubtreeProofs.Rust.SourceOwnerCallTransfer
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceTypedCallsTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def left : BalancedWord := .Pair (.Pair .Empty .Empty) .Empty
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
  .node .word 0 [], .node .word 1 [.owned 2, .owned 3], .node .word 0 []], fun a =>
  if a = 4 then some (.stack 77 1 4) else if a = 5 then some (.stack 77 2 5)
  else if a < 4 then some .box else none, fun a => decide (a < 6)⟩
private def packets : List ValueCell := [(.shared ⟨4, []⟩, .reference (encodeWord left)),
  (.shared ⟨5, []⟩, .reference (encodeWord .Empty))]
private theorem world_wf : world.WellFormed := by
  constructor
  · intro a
    change ((if a = 4 then some (.stack 77 1 4) else if a = 5 then some (.stack 77 2 5)
      else if a < 4 then some Class.box else none).isSome = true ↔ a < 6)
    split_ifs <;> simp_all
    all_goals omega
  · intro a ha
    exact of_decide_eq_true ha
private theorem readable : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
  intro p hp
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨[0, 1, 2, 3, 4], .shared rfl (.node
      (.cons (.owned rfl (.node (.cons (.owned rfl (.node .nil)) (.cons (.owned rfl (.node .nil)) .nil))))
        (.cons (.owned rfl (.node .nil)) .nil))), by simp [AliveOn, world]⟩
  · exact ⟨[5], .shared rfl (.node .nil), by simp [AliveOn, world]⟩
private theorem inputs_typed : SnapshotFieldsTyped (packets.map Prod.snd) (SourceEval.Types.inputs .compare) :=
  .cons (.shared (word_typed left)) (.cons (.shared (word_typed .Empty)) .nil)
private theorem compare_output : SourceEval.Types.callOutput .compare (SourceEval.Types.inputs .compare) = some .boolean := by
  simp only [SourceEval.Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true, SourceEval.Types.output]

-- A first-constructor mismatch returns before inspecting the deeper left word.
-- The old sufficient whole-word height bound fails, yet the actual helper and
-- the stronger full source/cost contract both succeed at call fuel one.
example : ¬ wordHeight left ≤ 1 := by decide +kernel
private def comparison := Helpers.callee 1 4 world (List.range 6) [] .compare packets
example : comparison.map (fun (_, packet, _) => packet) = some (.boolean false, .boolean false) := by with_unfolding_all rfl
example : ∃ final packet cost,
    comparison = some (final, packet, cost) ∧
    SourceEval.run SourceEval.Certificate.original.body 1 .compare (packets.map Prod.snd) = some (packet.2, cost) ∧
    SnapshotTyped packet.2 .boolean ∧ Readable final.memory final.live packet.1 packet.2 ∧ Preserves world final (List.range 6) := by
  have hs : comparison.isSome = true := by decide +kernel
  obtain ⟨⟨final, packet, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have hl : AliveOn world.live (List.range 6) := by intro a ha; exact decide_eq_true (List.mem_range.mp ha)
  have h := Helpers.callee_typed_respects 1 4 world (List.range 6) [] .compare packets final packet cost
    world_wf readable (by simp) hl ⟨_, .boolean, inputs_typed, compare_output⟩ hr
  exact ⟨final, packet, cost, hr, h.1,
    SourceEval.Types.original_run_typed 1 .compare _ _ _ _ _ inputs_typed compare_output h.1, h.2.1, h.2.2.2⟩
-- The exact ownership contract also covers this short-circuit success at
-- fuel one. The complete external owner ledger covers all four old Boxes.
example : ∃ final packet cost owners,
    comparison = some (final, packet, cost) ∧ Footprint final.memory packet.1 owners ∧
    OwnerFrame final (owners ++ [0, 1, 2, 3]) ∧ BoxCoverage final (owners ++ [0, 1, 2, 3]) := by
  have hs : comparison.isSome = true := by decide +kernel
  obtain ⟨⟨final, packet, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have frame : OwnerFrame world [0, 1, 2, 3] := by
    refine ⟨by decide +kernel, ?_, ?_⟩
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> rfl
    · intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl <;> rfl
  have coverage : BoxCoverage world [0, 1, 2, 3] := by
    intro a hc _
    change (if a = 4 then some (.stack 77 1 4) else if a = 5 then some (.stack 77 2 5)
      else if a < 4 then some Class.box else none) = some .box at hc
    split_ifs at hc <;> simp_all
    omega
  have footprint : FieldsFootprint world.memory (packets.map Prod.fst) [] :=
    .cons (.shared _) (.cons (.shared _) .nil)
  obtain ⟨owners, hp⟩ := Helpers.callee_owns 1 4 world (List.range 6) [] .compare packets final packet cost [] [0, 1, 2, 3]
    world_wf (by simp) readable (by intro a ha; exact decide_eq_true (List.mem_range.mp ha))
    ⟨_, .boolean, inputs_typed, compare_output⟩ footprint frame coverage hr
  exact ⟨final, packet, cost, owners, hr, hp⟩

example : (Helpers.callee 0 4 world [] [] .compare packets).isNone = true := by decide +kernel
example : (Helpers.callee 1 0 world [] [] .compare packets).isNone = true := by decide +kernel

-- Scalar width is still essential. The older concrete snapshot helper can
-- copy an arbitrary natural, whereas the expanded source rejects its u32 copy.
-- Independent input typing excludes this case from the stronger contract.
private def wideWorld : World := ⟨[.node .embedding 0 [.node .word 0 [], .number (2^32)]],
  fun a => if a = 0 then some (.stack 55 1 0) else none, fun a => decide (a = 0)⟩
private def widePackets : List ValueCell := [(.shared ⟨0, []⟩,
  .reference (.node .embedding 0 [.node .word 0 [], .number (2^32)]))]
example : (Helpers.execute 2 4 wideWorld .copyResult widePackets).isSome = true := by decide +kernel
example : SourceEval.operand (SourceEval.initialState (widePackets.map Prod.snd))
    (.copy (.field (.deref (.local 1)) none 1)) = none := by
  simp [SourceEval.operand, SourceEval.initialState, Locals.read_lift, readPlace, initialEnv, widePackets]
example : ¬ SnapshotTyped (.number (2^32)) .u32 := by
  intro h
  obtain ⟨number, he, bound⟩ := SourceEval.Types.typed_u32 h
  cases he
  omega

private def empty : World := ⟨[], fun _ => none, fun _ => false⟩
private def numbers : List ValueCell := [(.number 40, .number 40), (.number 2, .number 2)]
private def numericWorld := empty.stackCells 10 (numbers.map Prod.fst)
private def numericActive := initialActivation empty 10 4 numbers
private def locals : List Ty := [.u32, .u32, .u32, .option .u32]
private def good : SourceEval.Code := .step (.assign 0 (.use (.move (.field (.local 3) (some 1) 0)))) .ret
private def program : SourceEval.Code := .step (.storageLive 0) (.step (.storageLive 3)
  (.step (.call .checkedAdd [.move (.local 1), .move (.local 2)] 3)
    (.switch (.discriminant (.local 3)) [(.variant .optional 1, 0)] (some 1)
      good (.step .undefinedBehavior .done) (.step .undefinedBehavior .done))))
private def backend := Helpers.callee 8 16
private theorem empty_wf : empty.WellFormed := by simp [empty, World.WellFormed]
private theorem numbers_readable : ∀ p ∈ numbers, Readable empty.memory empty.live p.1 p.2 := by
  intro p hp
  simp only [numbers, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl <;> exact ⟨[], .number _, by simp [AliveOn]⟩
private theorem numeric_valid : numericActive.Valid numericWorld :=
  initialActivation_valid empty_wf 10 4 numbers_readable (by decide +kernel)
private theorem program_typed : SourceEval.Types.CodeConstraints locals .u32 program :=
  SourceEval.Types.checkCode_sound (by decide +kernel)
private theorem numeric_typed : LocalsTyped locals numericActive.state :=
  SourceEval.Types.initial_typed (.cons (.number (by decide +kernel)) (.cons (.number (by decide +kernel)) .nil)) rfl

example : (Calling.exec backend [] program numericWorld numericActive).map (fun (flow, cost) =>
    (match flow with | .returned _ _ (_, .number n) => n | _ => 0, cost.work.steps)) = some (42, 13) := by decide +kernel
example : ∃ flow cost,
    Calling.exec backend [] program numericWorld numericActive = some (flow, cost) ∧
    SourceEval.exec (SourceEval.run SourceEval.Certificate.original.body 8) program numericActive.state = some (flow.snapshot, cost) ∧
    flow.Valid [] ∧ SourceEval.Types.OutcomeTyped locals .u32 flow.snapshot := by
  have hs : (Calling.exec backend [] program numericWorld numericActive).isSome = true := by decide +kernel
  obtain ⟨⟨flow, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have h := Calling.exec_typed_spec (Helpers.callee_typed_respects 8 16) (SourceEval.Types.original_run_typed 8)
    program_typed numeric_valid (by simp) (empty_wf.stackCells _ _) numeric_typed hr
  exact ⟨flow, cost, hr, h.1, h.2.2.2⟩

end SourceTypedCallsTests
