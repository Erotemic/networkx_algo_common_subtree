import SubtreeProofs.Rust.SourceOwnerRecursive

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

-- Runtime equality instances are local to this executable regression module.
deriving instance BEq for Value
deriving instance BEq for Cell
deriving instance DecidableEq for LookupSource.Cost
deriving instance DecidableEq for SourceEval.Cost

private def pairWord : BalancedWord := .Pair .Empty .Empty
private def pairWorld : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
  .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 3, .owned 4]], fun a =>
  if a = 2 then some (.stack 90 1 2) else if a = 5 then some (.stack 90 2 5)
  else if a < 6 then some .box else none, fun a => decide (a < 6)⟩
private def pairParent : Activation := ⟨90, 3, fun s =>
  if s = 1 then some ⟨2, 2⟩ else if s = 2 then some ⟨5, 5⟩ else none,
  fun s => if s = 1 ∨ s = 2 then Slot.ofValue (encodeWord pairWord) else .empty⟩
private def pairPackets : List ValueCell := [(.shared ⟨2, []⟩, .reference (encodeWord pairWord)),
  (.shared ⟨5, []⟩, .reference (encodeWord pairWord)), (.node .table 0 [], encodeTable .Empty)]
private def pairAnswer : Value → Bool
  | .node .tuple 0 [.node .optional 1 [.node .embedding 0 [word, .number 1]], _] => word == encodeWord pairWord
  | .node .optional 1 [.node .embedding 0 [word, .number 1]] => word == encodeWord pairWord
  | _ => false

-- The second child hits the memo table after local 6's final use. This used to
-- fail at moving local 3. Both the evaluator and public maximum must now finish,
-- retain the caller's complete six cells, and retire all non-output new storage.
#eval show IO Unit from do
  for (function, fuel, steps) in [(SourceEval.Function.evaluate, 16, 2615), (.maximum, 17, 2704)] do
    let args := if function == .evaluate then pairPackets else pairPackets.take 2
    match Recursive.original 128 fuel pairWorld (List.range 6) [pairParent] function args with
    | none => throw (IO.userError s!"nonempty recursive {repr function} failed")
    | some (final, packet, cost) =>
      unless pairAnswer packet.2 && cost.work.steps == steps && cost.solverCalls == 5 do
        throw (IO.userError "wrong nonempty native result or exact source cost")
      unless final.memory.take 6 == pairWorld.memory && (List.range 6).all final.live do
        throw (IO.userError "nonempty recursive call changed caller bytes or liveness")
      match traceResources final.memory packet.1 (Slot.ofValue packet.2) with
      | none => throw (IO.userError "output resource readback failed")
      | some output =>
        let completeOwners := output.owners ++ pairParent.owners final
        unless decide completeOwners.Nodup do
          throw (IO.userError "duplicate recursive output/caller Box owners")
        unless completeOwners.all (fun a => decide (final.classes a = some .box) && final.live a) do
          throw (IO.userError "recursive owner is not a live Box")
        unless (List.range final.memory.length).all (fun a =>
            if decide (final.classes a = some .box) && final.live a then decide (a ∈ completeOwners) else true) do
          throw (IO.userError "live recursive Box missing from complete output/caller ledger")
        unless (List.range final.memory.length).all (fun a =>
            final.live a == decide (a < 6 ∨ a ∈ output.owners)) do
          throw (IO.userError "callee roots or discarded table owners remain live")
      match SourceEval.run SourceEval.Certificate.original.body fuel function (args.map Prod.snd) with
      | none => throw (IO.userError "nonempty pinned source failed")
      | some (value, sourceCost) =>
        unless value == packet.2 && decide (sourceCost = cost) do
          throw (IO.userError "nonempty complete source value/table or cost mismatch")

end SourceRecursiveExecutionTests
