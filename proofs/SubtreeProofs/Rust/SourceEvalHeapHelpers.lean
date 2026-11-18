module

public import SubtreeProofs.Rust.SourceHeapHelperWorld
public import SubtreeProofs.Rust.SourceEvalHelperSafety

/-! Reuse the existing concrete helper executors over the mixed memory prefix.
Only actual cells enter those executors; output metadata is read back from the
actual result cell. Source correspondence consumes the already proved local
helper contract, not a desired evaluator result. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

def finish (budget : Nat) (world : World) (raw : Option (Cell × Memory × LookupSource.Cost)) :
    Option (World × ValueCell × SourceEval.Cost) := do
  let (cell, memory, cost) ← raw
  let final := world.boxSuffix memory
  let packet ← readPacket budget final cell
  some (final, packet, Legacy.costMap cost)

def lookup (fuel budget : Nat) (world : World) (function : LookupSource.Function) (packets : List ValueCell) :
    Option (World × ValueCell × SourceEval.Cost) :=
  finish budget world (Heap.run LookupSource.Program.body fuel function (packets.map Prod.fst) world.memory)

def memo (fuel budget : Nat) (world : World) (function : MemoSource.Function) (packets : List ValueCell) :
    Option (World × ValueCell × SourceEval.Cost) :=
  finish budget world (MemoSource.Heap.run MemoSource.Program.body fuel function (packets.map Prod.fst) world.memory)

theorem finish_run {budget : Nat} {world : World} {raw : Option (Cell × Memory × LookupSource.Cost)}
    {cell : Cell} {memory : Memory} {cost : LookupSource.Cost} {value : Value}
    (hr : raw = some (cell, memory, cost))
    (hp : readPacket budget (world.boxSuffix memory) cell = some (cell, value)) :
    finish budget world raw = some (world.boxSuffix memory, (cell, value), Legacy.costMap cost) := by
  simp only [finish, hr, hp, Bind.bind, Option.bind]

theorem finish_spec {budget : Nat} {world final : World} {raw : Option (Cell × Memory × LookupSource.Cost)}
    {cell : Cell} {memory : Memory} {oldCost : LookupSource.Cost} {packet : ValueCell} {cost : SourceEval.Cost}
    (hw : world.WellFormed) (hr : raw = some (cell, memory, oldCost)) (he : Extends world.memory memory)
    (h : finish budget world raw = some (final, packet, cost)) :
    final = world.boxSuffix memory ∧ packet.1 = cell ∧ cost = Legacy.costMap oldCost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∀ guards, Keeps world final guards := by
  simp only [finish, hr, Bind.bind, Option.bind] at h
  cases hp : readPacket budget (world.boxSuffix memory) cell with
  | none => simp [hp] at h
  | some found =>
    simp only [hp, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    obtain ⟨hc, hv⟩ := readPacket_spec hp
    exact ⟨rfl, hc, rfl, hv, hw.boxSuffix he, world.boxSuffix_keeps hw he⟩

theorem lookup_spec (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : LookupSource.Function) (packets : List ValueCell) {value : Value} {oldCost : LookupSource.Cost}
    (hb : Legacy.FieldsBounded (packets.map Prod.snd))
    (hp : RepresentsFields world.memory (packets.map Prod.fst) (packets.map Prod.snd))
    (hs : Control.run LookupSource.Certificate.original.body fuel function (packets.map Prod.snd) = some (value, oldCost))
    {packet : ValueCell} {cost : SourceEval.Cost}
    (h : lookup fuel budget world function packets = some (final, packet, cost)) :
    SourceEval.run SourceEval.Certificate.original.body fuel (SourceEval.Helpers.lookupFunction function) (packets.map Prod.snd) =
        some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∀ guards, Keeps world final guards := by
  obtain ⟨cell, memory, hr, hv, he, _⟩ := Heap.certified_run_spec fuel function world.memory _ _ _ _ hp hs
  obtain ⟨rfl, hcell, rfl, hread, hworld, hkeep⟩ := finish_spec hw hr he h
  obtain ⟨used, hgraph, halive⟩ := hread
  have hvalue : packet.2 = value := represents_unique (hcell ▸ hgraph.represents) hv
  have hsource := (SourceEval.Helpers.lookup_run fuel function _ _ oldCost hb hs).2
  exact ⟨by simpa only [hvalue] using hsource, ⟨used, hgraph, halive⟩, hworld, hkeep⟩

theorem memo_spec (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : MemoSource.Function) (packets : List ValueCell) {value : Value} {oldCost : LookupSource.Cost}
    (hb : Legacy.FieldsBounded (packets.map Prod.snd))
    (hp : RepresentsFields world.memory (packets.map Prod.fst) (packets.map Prod.snd))
    (hs : MemoSource.sourceRun MemoSource.Certificate.original.body fuel function (packets.map Prod.snd) = some (value, oldCost))
    {packet : ValueCell} {cost : SourceEval.Cost}
    (h : memo fuel budget world function packets = some (final, packet, cost)) :
    SourceEval.run SourceEval.Certificate.original.body fuel (SourceEval.Helpers.memoFunction function) (packets.map Prod.snd) =
        some (packet.2, cost) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      ∀ guards, Keeps world final guards := by
  obtain ⟨cell, memory, hr, hv, he, _⟩ := MemoSource.Heap.certified_run_spec fuel function world.memory _ _ _ _ hp hs
  obtain ⟨rfl, hcell, rfl, hread, hworld, hkeep⟩ := finish_spec hw hr he h
  obtain ⟨used, hgraph, halive⟩ := hread
  have hvalue : packet.2 = value := represents_unique (hcell ▸ hgraph.represents) hv
  have hsource := (SourceEval.Helpers.memo_run fuel function _ _ oldCost hb hs).2
  exact ⟨by simpa only [hvalue] using hsource, ⟨used, hgraph, halive⟩, hworld, hkeep⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
