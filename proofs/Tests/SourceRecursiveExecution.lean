import SubtreeProofs.Rust.SourceEvalRecursiveRefinement

/-! Executable regression of the pinned evaluator through parsed recursive
entry, helper calls and checked cleanup. This runtime test complements the
kernel-checked conditional source/native theorems; it is not universal totality. -/

namespace SourceRecursiveExecutionTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

private def world : World := ⟨[.node .word 0 [], .node .word 0 []], fun a =>
  if a = 0 then some (.stack 90 1 0) else if a = 1 then some (.stack 90 2 1) else none,
  fun a => decide (a < 2)⟩
private def parent : Activation := ⟨90, 3, fun s =>
  if s = 1 then some ⟨0, 0⟩ else if s = 2 then some ⟨1, 1⟩ else none,
  fun s => if s = 1 ∨ s = 2 then .node .word 0 [] else .empty⟩
private def packets : List ValueCell := [(.shared ⟨0, []⟩, .reference (encodeWord .Empty)),
  (.shared ⟨1, []⟩, .reference (encodeWord .Empty)), (.node .table 0 [], encodeTable .Empty)]

private def emptyAnswer : Value → Bool
  | .node .tuple 0 [.node .optional 1 [.node .embedding 0 [.node .word 0 [], .number 0]],
      .node .table 1 [.boxed (.node .entry 0 [.node .word 0 [], .node .word 0 [],
        .node .embedding 0 [.node .word 0 [], .number 0]]), .boxed (.node .table 0 [])]] => true
  | _ => false

-- This runs the actual 113-local parsed declaration, lookup/insert backends and
-- stack cleanup, with a complete suspended caller holding both input roots.
#eval show IO Unit from do
  match Recursive.original 32 8 world [0, 1] [parent] .evaluate packets with
  | none => throw (IO.userError "cold empty recursive evaluator failed")
  | some (final, packet, cost) =>
    unless emptyAnswer packet.2 do throw (IO.userError "wrong cold empty native result/table")
    unless cost.work.steps == 271 && cost.work.events.allocations == 2 && cost.solverCalls == 1 do
      throw (IO.userError "wrong complete recursive evaluator cost")
    unless (List.range final.memory.length).filter final.live == [0, 1, 22, 23] do
      throw (IO.userError "caller roots, output owners or callee cleanup changed")
    match SourceEval.run SourceEval.Certificate.original.body 8 .evaluate (packets.map Prod.snd) with
    | none => throw (IO.userError "pinned source evaluator failed")
    | some (value, sourceCost) =>
      unless emptyAnswer value && sourceCost.work.steps == cost.work.steps &&
          sourceCost.work.events.allocations == cost.work.events.allocations && sourceCost.solverCalls == cost.solverCalls do
        throw (IO.userError "recursive/source complete result or cost mismatch")

end SourceRecursiveExecutionTests
