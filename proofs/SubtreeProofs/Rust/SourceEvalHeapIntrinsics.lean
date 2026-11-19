module

public import SubtreeProofs.Rust.SourceEvalHeapLookup

/-! Box and checked-add execute actual cells and retain source entry costs.
The ordinary dispatcher reuses six completed helper interpreters; choice,
recursive evaluator and public-core calls are not supplied as hidden answers. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource LookupSource.Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

def numberOptionCell : Option Nat → Cell
  | none => .node .optional 0 []
  | some value => .node .optional 1 [.number value]

theorem numberOption_graph (memory : Memory) (value : Option Nat) :
    Graph memory (numberOptionCell value) (encodeNumberOption value) [] := by
  cases value with
  | none => exact .node .nil
  | some n => exact .node (.cons (.number n) .nil)

def boxNew (fuel : Nat) (world : World) (packets : List ValueCell) : Option (World × ValueCell × SourceEval.Cost) :=
  match fuel, packets with
  | _ + 1, [(cell, value)] => some (world.allocate .box cell, (.owned world.memory.length, .boxed value), Cost.entry .boxNew)
  | _, _ => none

theorem boxNew_total (fuel : Nat) {world : World} (hw : world.WellFormed) {cell : Cell} {value : Value}
    (h : Readable world.memory world.live cell value) :
    boxNew (fuel + 1) world [(cell, value)] =
        some (world.allocate .box cell, (.owned world.memory.length, .boxed value), Cost.entry .boxNew) ∧
      SourceEval.run SourceEval.Certificate.original.body (fuel + 1) .boxNew [value] = some (.boxed value, Cost.entry .boxNew) ∧
      Readable (world.allocate .box cell).memory (world.allocate .box cell).live (.owned world.memory.length) (.boxed value) ∧
      (world.allocate .box cell).WellFormed ∧ (∀ guards, Keeps world (world.allocate .box cell) guards) ∧
      (world.allocate .box cell).classes world.memory.length = some .box := by
  obtain ⟨used, hg, hl⟩ := h
  have hs := world.allocate_spec .box cell
  refine ⟨rfl, rfl, ⟨used ++ [world.memory.length], .owned hs.2.1 (hg.mono hs.1), ?_⟩,
    hw.allocate _ _, world.allocate_keeps hw _ _, hs.2.2.1⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact (world.allocate_keeps hw .box cell used).alive a ha (hl a ha)
  · simpa only [List.mem_singleton.mp ha] using hs.2.2.2.1

def checkedAdd (fuel : Nat) (world : World) (packets : List ValueCell) : Option (World × ValueCell × SourceEval.Cost) :=
  match fuel, packets with
  | _ + 1, [(.number left, _), (.number right, _)] =>
    if left < 2^32 ∧ right < 2^32 then
      let value := checkedAdd32 left right
      some (world, (numberOptionCell value, encodeNumberOption value), Cost.entry .checkedAdd)
    else none
  | _, _ => none

theorem checkedAdd_total (fuel : Nat) {world : World} (hw : world.WellFormed) (left right : Nat)
    (hl : left < 2^32) (hr : right < 2^32) :
    checkedAdd (fuel + 1) world [(.number left, .number left), (.number right, .number right)] =
        some (world, (numberOptionCell (checkedAdd32 left right), encodeNumberOption (checkedAdd32 left right)), Cost.entry .checkedAdd) ∧
      SourceEval.run SourceEval.Certificate.original.body (fuel + 1) .checkedAdd [.number left, .number right] =
        some (encodeNumberOption (checkedAdd32 left right), Cost.entry .checkedAdd) ∧
      Readable world.memory world.live (numberOptionCell (checkedAdd32 left right)) (encodeNumberOption (checkedAdd32 left right)) ∧
      world.WellFormed ∧ (∀ guards, Keeps world world guards) := by
  refine ⟨by simp only [checkedAdd, hl, hr, and_self, ite_true],
    by simp only [SourceEval.run, hl, hr, and_self, ite_true],
    ⟨[], numberOption_graph _ _, by simp [AliveOn]⟩, hw, Keeps.refl world⟩

def execute (fuel budget : Nat) (world : World) (function : SourceEval.Function) (packets : List ValueCell) :
    Option (World × ValueCell × SourceEval.Cost) :=
  match function with
  | .copyWord => lookup fuel budget world .copyWord packets
  | .compare => lookup fuel budget world .compare packets
  | .copyResult => lookup fuel budget world .copyResult packets
  | .lookup => lookup fuel budget world .lookup packets
  | .concatenate => memo fuel budget world .concatenate packets
  | .insert => memo fuel budget world .insert packets
  | .boxNew => boxNew fuel world packets
  | .checkedAdd => checkedAdd fuel world packets
  | .chooseLonger | .evaluate | .maximum => none

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
