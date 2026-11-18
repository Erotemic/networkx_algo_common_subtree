module

import SubtreeProofs.Rust.SourceEvalHelperCalls
import all SubtreeProofs.Rust.SourceHeapReadback
import all SubtreeProofs.Rust.SourceHeapResources
import all SubtreeProofs.Rust.SourceHeapGraphTrace
import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

@[expose] section

namespace SourceHelperCallsTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def result : CommonEmbedding := ⟨.Empty, 4#u32⟩
private def table : MemoTable := .Entry ⟨.Empty, .Empty, result⟩ .Empty
private def entry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [], .node .embedding 0 [.node .word 0 [], .number 4]]
private def oldTable : Cell := .node .table 1 [.owned 2, .owned 3]
private def base : World := ⟨[.number 99, .number 88, entry, .node .table 0 [], .node .word 0 []],
  fun a => if a = 2 ∨ a = 3 then some .box else if a < 5 then some (.stack 77 a 0) else none,
  fun a => decide (0 < a ∧ a < 5)⟩
private def pl : Pointer := ⟨2, [0]⟩
private def pr : Pointer := ⟨2, [1]⟩
private def pc : Pointer := ⟨2, [2]⟩
private def packets : List ValueCell := [(oldTable, encodeTable table),
  (.shared pl, .reference (encodeWord .Empty)), (.shared pr, .reference (encodeWord .Empty)),
  (.shared pc, .reference (encodeResult result))]
private def world := base.stackCells 10 (packets.map Prod.fst)
private def active := initialActivation base 10 6 packets

private theorem well_formed : base.WellFormed := by
  constructor
  · intro a
    by_cases hb : a = 2 ∨ a = 3 <;> by_cases ha : a < 5 <;> simp [base, hb, ha]; omega
  · intro a ha
    simp only [base, decide_eq_true_eq] at ha
    exact ha.2
private theorem table_graph : Graph base.memory oldTable (encodeTable table) [2, 3] :=
  .node (.cons (.owned rfl (.node (.cons (.node .nil) (.cons (.node .nil)
    (.cons (.node (.cons (.node .nil) (.cons (.number 4) .nil))) .nil)))))
    (.cons (.owned rfl (.node .nil)) .nil))
private theorem readable : ∀ p ∈ packets, Readable base.memory base.live p.1 p.2 := by
  intro p hp
  simp only [packets, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl
  · exact ⟨[2, 3], table_graph, by simp [AliveOn, base]⟩
  · exact ⟨[2], .shared rfl (.node .nil), by simp [AliveOn, base]⟩
  · exact ⟨[2], .shared rfl (.node .nil), by simp [AliveOn, base]⟩
  · exact ⟨[2], .shared rfl (.node (.cons (.node .nil) (.cons (.number 4) .nil))), by simp [AliveOn, base]⟩
private theorem active_valid : active.Valid world := initialActivation_valid well_formed 10 6 readable (by decide +kernel)
private theorem world_valid : world.WellFormed := well_formed.stackCells _ _

-- Input Box owners and query references deliberately alias. The old dead
-- stack cell stays dead; old class identities survive the fresh Box suffix.
example : (Helpers.execute 8 32 world .insert packets).map (fun (after, packet, _) =>
    ((after.memory.length, after.live 0, after.classes 0), (after.classes 9, after.classes 10,
      traceResources after.memory packet.1 (Slot.ofValue packet.2)))) =
    some ((11, false, some (.stack 77 0 0)), (some .box, some .box,
      some ⟨[9, 2, 3, 10], [9, 2, 3, 10], []⟩)) := by decide +kernel
example : (Helpers.execute 8 0 world .insert packets).isNone = true := by decide +kernel
example : (Helpers.execute 0 32 world .insert packets).isNone = true := by decide +kernel
example : snapshot 3 ([] : Memory) (.owned 0) = none := by decide +kernel
example : snapshot 3 [.owned 0] (.owned 0) = none := by decide +kernel

-- Existing helper source/ownership contracts are instantiated on the actual
-- mixed prefix and allowed aliases, including the transferred old table tail.
example : ∃ cell memory cost old owners,
    Helpers.memo 8 32 world .insert packets = some (world.boxSuffix memory,
      (cell, encodeTable (.Entry ⟨.Empty, .Empty, result⟩ table)), SourceEval.Legacy.costMap cost) ∧
    Footprint world.memory oldTable old ∧ Footprint memory cell owners ∧
    owners.Perm (old ++ List.range' world.memory.length (memory.length - world.memory.length)) ∧
    AliveOn (world.boxSuffix memory).live owners ∧
    ∃ copied tail, cell = .node .table 1 [copied, .owned tail] ∧ memory[tail]? = some oldTable := by
  have hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2 := by
    intro p hm
    obtain ⟨used, hg, hl⟩ := readable p hm
    exact ⟨used, hg.mono (base.stackCells_keeps well_formed 10 (packets.map Prod.fst) used).memory,
      fun a ha => (base.stackCells_keeps well_formed 10 (packets.map Prod.fst) used).alive a ha (hl a ha)⟩
  obtain ⟨cell, memory, cost, old, owners, he, _, _, ht, ho, hperm, _, _, hl, htail, _, _⟩ :=
    Helpers.insert_total table .Empty .Empty result 8 32 (by decide +kernel) world_valid oldTable pl pr pc
      (hp (oldTable, encodeTable table) (by simp [packets]))
      (hp (.shared pl, .reference (encodeWord .Empty)) (by simp [packets]))
      (hp (.shared pr, .reference (encodeWord .Empty)) (by simp [packets]))
      (hp (.shared pc, .reference (encodeResult result)) (by simp [packets])) (by decide +kernel)
  obtain ⟨copied, tail, hs, hh, _⟩ := htail
  exact ⟨cell, memory, cost, old, owners, he, ht, ho, hperm, hl, copied, tail, hs, hh⟩

private def preparedWorld := world.allocate (.stack 10 0 9) (.node .tuple 0 [])
private def prepared : Activation := { active with roots := active.roots.set 0 (some ⟨9, 9⟩), state := active.state.set 0 .empty }
private theorem open_return : Derived.storageLive world active [] 0 = some (preparedWorld, prepared) := by with_unfolding_all rfl
private theorem prepared_valid : prepared.Valid preparedWorld :=
  (Derived.storageLive_spec active_valid (by simp) world_valid open_return).valid
private theorem prepared_world_valid : preparedWorld.WellFormed := world_valid.allocate _ _
private def args : List SourceEval.Operand := [.move (.local 1), .move (.local 2), .move (.local 3), .move (.local 4)]
private def masks := (((prepared.state.set 1 .empty).set 2 .empty).set 3 .empty).set 4 .empty
private def current : Resources := ⟨[9, 2, 3, 5, 2, 6, 2, 7, 2, 8], [2, 3], [2, 2, 2]⟩
private theorem current_scan : prepared.scan preparedWorld = some current := by with_unfolding_all rfl
private theorem args_run : operands preparedWorld prepared.roots (current.loans ++ ([] : List Nat)) prepared.state args = some (packets, masks) := by with_unfolding_all rfl

private theorem ready : ∀ scanned suspended values after, prepared.scan preparedWorld = some scanned →
    scanCallers preparedWorld [] = some suspended →
    operands preparedWorld prepared.roots (scanned.loans ++ suspended.reads) prepared.state args = some (values, after) →
    Helpers.Ready 8 .insert values := by
  intro scanned suspended values after hs hc he
  rw [current_scan] at hs
  cases hs
  change some ({} : Resources) = some suspended at hc
  cases hc
  rw [args_run] at he
  cases he
  exact .insert table .Empty .Empty result oldTable pl pr pc (by decide +kernel)

private def callRun := Derived.call (Helpers.callee 8 32) preparedWorld prepared [] .insert args 0

-- Complete caller argument moves, actual helper execution and guarded result
-- initialization preserve original source action/cost and the actual frame.
example : (callRun.map (fun (after, next, cost) =>
    (after.memory.length, after.live 0, next.roots 0,
      (List.range 4).map (fun n => (next.state (n + 1)).dropWork.boxes), cost.work.events.allocations))) =
    some (12, false, some ⟨9, 9⟩, [0, 0, 0, 0], 2) := by decide +kernel
example : (Derived.call (Helpers.callee 8 32) (preparedWorld.retire [2]) prepared [] .insert args 0).isNone = true := by decide +kernel
example : (Derived.call (Helpers.callee 8 32) (preparedWorld.write 9 (.number 1))
    { prepared with state := prepared.state.set 0 (.number 1) } [] .insert args 0).isNone = true := by decide +kernel
example : ∃ final after cost, callRun = some (final, after, cost) ∧
    SourceEval.action (SourceEval.run SourceEval.Certificate.original.body 8) prepared.state (.call .insert args 0) = some (after.state, cost) ∧
    after.Valid final ∧ final.WellFormed := by
  have hs : callRun.isSome = true := by decide +kernel
  obtain ⟨⟨final, after, cost⟩, hr⟩ := Option.isSome_iff_exists.mp hs
  have h := Derived.call_spec (Helpers.callee_respects 8 32) prepared_valid (by simp) prepared_world_valid .insert args 0 ready hr
  exact ⟨final, after, cost, hr, h.1, h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

-- All other ordinary backends and both intrinsics execute real cells too.
private def words : List ValueCell := [(.shared pl, .reference (encodeWord .Empty)), (.shared pr, .reference (encodeWord .Empty))]
example : (Helpers.execute 8 16 world .copyWord (words.take 1)).isSome = true := by decide +kernel
example : (Helpers.execute 8 16 world .compare words).isSome = true := by decide +kernel
example : (Helpers.execute 8 16 world .copyResult [(.shared pc, .reference (encodeResult result))]).isSome = true := by decide +kernel
example : (Helpers.execute 8 16 world .concatenate words).isSome = true := by decide +kernel
example : (Helpers.execute 8 16 preparedWorld .lookup [(.shared ⟨5, []⟩, .reference (encodeTable table)),
    (.shared pl, .reference (encodeWord .Empty)), (.shared pr, .reference (encodeWord .Empty))]).isSome = true := by decide +kernel
example : (Helpers.execute 1 0 world .boxNew [(.number 7, .number 7)]).map (fun (after, _, cost) =>
    (after.memory.length, after.classes 9, after.live 9, cost.work.events.allocations)) = some (10, some .box, true, 1) := by decide +kernel
example : (Helpers.execute 1 0 world .checkedAdd [(.number 4294967295, .number 4294967295), (.number 1, .number 1)]).map
    (fun (after, packet, _) => (after.memory.length, match packet.1 with | .node .optional tag fields => some (tag, fields.length) | _ => none)) =
    some (9, some (0, 0)) := by decide +kernel
example : (Helpers.execute 1 0 world .checkedAdd [(.number 4294967294, .number 4294967294), (.number 1, .number 1)]).map
    (fun (_, packet, _) => match packet.1 with | .node .optional 1 [.number n] => some n | _ => none) =
    some (some 4294967295) := by decide +kernel
example : (Helpers.execute 1 0 world .checkedAdd [(.number 4294967296, .number 4294967296), (.number 1, .number 1)]).isNone = true := by decide +kernel

end SourceHelperCallsTests

end
