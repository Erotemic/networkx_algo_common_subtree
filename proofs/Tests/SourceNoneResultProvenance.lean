import SubtreeProofs.Rust.SourceNoneResultProvenance

/-! None witness provenance permits a returned table owning older cells. -/

namespace SourceNoneResultProvenanceTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def entry : Cell := .node .entry 0 [.node .word 0 [], .node .word 0 [],
  .node .embedding 0 [.node .word 0 [], .number 0]]
private def memo : MemoTable := .Entry ⟨.Empty, .Empty, ⟨.Empty, 0#u32⟩⟩ .Empty
private def world : World := ⟨[entry, .node .table 0 []], fun a => if a < 2 then some .box else none,
  fun a => decide (a < 2)⟩
private def table : Cell := .node .table 1 [.owned 0, .owned 1]
private def packet : Cell := .node .tuple 0 [.node .optional 0 [], table]

private theorem entry_graph : Graph world.memory entry
    (.node .entry 0 [encodeWord .Empty, encodeWord .Empty, encodeResult ⟨.Empty, 0#u32⟩]) [] :=
  .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons (.node .nil) (.cons (.number 0) .nil))) .nil)))

private theorem packet_readable : Readable world.memory world.live packet (SourceEval.Evaluator.encodeOutput none memo) := by
  refine ⟨[0, 1], .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl entry_graph)
    (.cons (.owned rfl (.node .nil)) .nil))) .nil)), ?_⟩
  simp [AliveOn, world]

private theorem packet_footprint : Footprint world.memory packet [0, 1] := by
  have head : Footprint world.memory entry [] :=
    .node (.cons (.node .nil) (.cons (.node .nil) (.cons (.node (.cons (.node .nil) (.cons (.number 0) .nil))) .nil)))
  exact .node (.cons (.node .nil) (.cons (.node (.cons (.owned rfl head) (.cons (.owned rfl (.node .nil)) .nil))) .nil))

example (bound : Nat) : ResultOwnersAbove bound world.memory packet :=
  SourceEval.Evaluator.none_result_owners_above bound packet_readable

example : ¬ CellOwnersAbove 2 world.memory packet := by
  intro whole
  have impossible := whole [0, 1] packet_footprint 0 (by simp)
  omega

end SourceNoneResultProvenanceTests
