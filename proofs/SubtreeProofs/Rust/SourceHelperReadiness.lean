module

public import SubtreeProofs.Rust.SourceHelperNativeInputs
public import SubtreeProofs.Rust.SourceEvalRecursiveCalls

/-! Readable, independently typed helper arguments determine finite sufficient
native call fuel. No helper result, source success or cache correctness is an
input. Interpreted recursive functions retain their separate totality obligation. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Partial Partial.Addressed Storage verified_ordered_core

theorem typed_packets_cons {packets : List ValueCell} {ty : Ty} {types : List Ty}
    (h : SnapshotFieldsTyped (packets.map Prod.snd) (ty :: types)) :
    ∃ packet rest, packets = packet :: rest ∧ SnapshotTyped packet.2 ty ∧
      SnapshotFieldsTyped (rest.map Prod.snd) types := by
  cases packets with
  | nil => cases h
  | cons packet rest => cases h with
    | cons first tail => exact ⟨packet, rest, rfl, first, tail⟩

theorem typed_packets_nil {packets : List ValueCell}
    (h : SnapshotFieldsTyped (packets.map Prod.snd) []) : packets = [] := by
  cases packets with
  | nil => rfl
  | cons packet rest => cases h

theorem typed_shared_packet {world : World} {packet : ValueCell} {ty : Ty}
    (hp : Readable world.memory world.live packet.1 packet.2)
    (ht : SnapshotTyped packet.2 (.shared ty)) :
    ∃ pointer inner, packet = (.shared pointer, .reference inner) ∧ SnapshotTyped inner ty := by
  rcases packet with ⟨cell, value⟩
  obtain ⟨inner, rfl, typed⟩ := ht.shared_value
  obtain ⟨_, graph, _⟩ := hp
  cases graph
  exact ⟨_, inner, rfl, typed⟩

theorem typed_word_packet {world : World} {packet : ValueCell}
    (hp : Readable world.memory world.live packet.1 packet.2)
    (ht : SnapshotTyped packet.2 (.shared (.adt .word))) :
    ∃ pointer word, packet = (.shared pointer, .reference (encodeWord word)) := by
  obtain ⟨pointer, inner, rfl, typed⟩ := typed_shared_packet hp ht
  obtain ⟨word, rfl⟩ := typed.native_word
  exact ⟨pointer, word, rfl⟩

theorem typed_result_packet {world : World} {packet : ValueCell}
    (hp : Readable world.memory world.live packet.1 packet.2)
    (ht : SnapshotTyped packet.2 (.shared (.adt .embedding))) :
    ∃ pointer result, packet = (.shared pointer, .reference (encodeResult result)) := by
  obtain ⟨pointer, inner, rfl, typed⟩ := typed_shared_packet hp ht
  obtain ⟨result, rfl⟩ := typed.native_result
  exact ⟨pointer, result, rfl⟩

theorem typed_table_packet {world : World} {packet : ValueCell}
    (hp : Readable world.memory world.live packet.1 packet.2)
    (ht : SnapshotTyped packet.2 (.shared (.adt .table))) :
    ∃ pointer table, packet = (.shared pointer, .reference (encodeTable table)) := by
  obtain ⟨pointer, inner, rfl, typed⟩ := typed_shared_packet hp ht
  obtain ⟨table, rfl⟩ := typed.native_table
  exact ⟨pointer, table, rfl⟩

theorem typed_number_packet {world : World} {packet : ValueCell}
    (hp : Readable world.memory world.live packet.1 packet.2)
    (ht : SnapshotTyped packet.2 .u32) :
    ∃ number, packet = (.number number, .number number) ∧ number < 2^32 := by
  rcases packet with ⟨cell, value⟩
  obtain ⟨number, rfl, bound⟩ := Types.typed_u32 ht
  obtain ⟨_, graph, _⟩ := hp
  cases graph
  exact ⟨number, rfl, bound⟩

theorem Ready.enlarge {small large : Nat} {function : Function} {packets : List ValueCell}
    (h : Ready small function packets) (bound : small ≤ large) : Ready large function packets := by
  cases h <;> constructor <;> omega

theorem typed_ready_exists {world : World} {function : Function} {packets : List ValueCell}
    (helper : Recursive.interpreted function = false)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (ht : Derived.TypedReady world function packets) : ∃ fuel, Ready fuel function packets := by
  obtain ⟨types, ty, typed, output⟩ := ht
  by_cases box : function = .boxNew
  · subst function
    cases types with
    | nil => cases output
    | cons inner rest => cases rest with
      | cons _ _ => cases output
      | nil =>
        obtain ⟨packet, rest, rfl, _, tail⟩ := typed_packets_cons typed
        obtain rfl := typed_packets_nil tail
        exact ⟨1, .boxNew packet.1 packet.2 (by omega)⟩
  have standard := (Types.callOutput_standard box output).1
  rw [standard] at typed
  cases function with
  | copyWord =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain rfl := typed_packets_nil tail0
    obtain ⟨p0, w0, rfl⟩ := typed_word_packet (hp _ (by simp)) t0
    exact ⟨wordHeight w0,  .copyWord w0 p0 (by omega)⟩
  | compare =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain ⟨a1, rest1, rfl, t1, tail1⟩ := typed_packets_cons tail0
    obtain rfl := typed_packets_nil tail1
    obtain ⟨p0, w0, rfl⟩ := typed_word_packet (hp _ (by simp)) t0
    obtain ⟨p1, w1, rfl⟩ := typed_word_packet (hp _ (by simp)) t1
    exact ⟨wordHeight w0,  .compare w0 w1 p0 p1 (by omega)⟩
  | copyResult =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain rfl := typed_packets_nil tail0
    obtain ⟨p0, w0, rfl⟩ := typed_result_packet (hp _ (by simp)) t0
    exact ⟨wordHeight w0.word + 1,  .copyResult w0 p0 (by omega)⟩
  | lookup =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain ⟨a1, rest1, rfl, t1, tail1⟩ := typed_packets_cons tail0
    obtain ⟨a2, rest2, rfl, t2, tail2⟩ := typed_packets_cons tail1
    obtain rfl := typed_packets_nil tail2
    obtain ⟨p0, w0, rfl⟩ := typed_table_packet (hp _ (by simp)) t0
    obtain ⟨p1, w1, rfl⟩ := typed_word_packet (hp _ (by simp)) t1
    obtain ⟨p2, w2, rfl⟩ := typed_word_packet (hp _ (by simp)) t2
    exact ⟨lookupDepth w0 w1 w2,  .lookup w0 w1 w2 p0 p1 p2 (by omega)⟩
  | concatenate =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain ⟨a1, rest1, rfl, t1, tail1⟩ := typed_packets_cons tail0
    obtain rfl := typed_packets_nil tail1
    obtain ⟨p0, w0, rfl⟩ := typed_word_packet (hp _ (by simp)) t0
    obtain ⟨p1, w1, rfl⟩ := typed_word_packet (hp _ (by simp)) t1
    exact ⟨MemoSource.concatenateDepth w0 w1,  .concatenate w0 w1 p0 p1 (by omega)⟩
  | insert =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain ⟨a1, rest1, rfl, t1, tail1⟩ := typed_packets_cons tail0
    obtain ⟨a2, rest2, rfl, t2, tail2⟩ := typed_packets_cons tail1
    obtain ⟨a3, rest3, rfl, t3, tail3⟩ := typed_packets_cons tail2
    obtain rfl := typed_packets_nil tail3
    rcases a0 with ⟨c0, v0⟩
    obtain ⟨w0, rfl⟩ := t0.native_table
    obtain ⟨p1, w1, rfl⟩ := typed_word_packet (hp _ (by simp)) t1
    obtain ⟨p2, w2, rfl⟩ := typed_word_packet (hp _ (by simp)) t2
    obtain ⟨p3, w3, rfl⟩ := typed_result_packet (hp _ (by simp)) t3
    exact ⟨MemoSource.insertDepth w1 w2 w3,  .insert w0 w1 w2 w3 c0 p1 p2 p3 (by omega)⟩
  | checkedAdd =>
    obtain ⟨a0, rest0, rfl, t0, tail0⟩ := typed_packets_cons typed
    obtain ⟨a1, rest1, rfl, t1, tail1⟩ := typed_packets_cons tail0
    obtain rfl := typed_packets_nil tail1
    obtain ⟨n0, rfl, b0⟩ := typed_number_packet (hp _ (by simp)) t0
    obtain ⟨n1, rfl, b1⟩ := typed_number_packet (hp _ (by simp)) t1
    exact ⟨1,  .checkedAdd n0 n1 (by omega) b0 b1⟩
  | boxNew => exact False.elim (box rfl)
  | chooseLonger | evaluate | maximum => cases helper

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
