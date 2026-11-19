import SubtreeProofs.Rust.SourceMaximumTotality

namespace SourceMaximumExecutionTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed Storage
open SourceEval.Addressed verified_ordered_core

deriving instance BEq for Value
deriving instance BEq for Cell
deriving instance DecidableEq for LookupSource.Cost
deriving instance DecidableEq for SourceEval.Cost

private def word : BalancedWord := .Pair .Empty .Empty
private def world : World := ⟨[.node .word 0 [], .node .word 0 [], .node .word 1 [.owned 0, .owned 1],
  .node .word 0 [], .node .word 0 [], .node .word 1 [.owned 3, .owned 4]], fun a =>
  if a = 2 then some (.stack 90 1 2) else if a = 5 then some (.stack 90 2 5)
  else if a < 6 then some .box else none, fun a => decide (a < 6)⟩
private def parent : Activation := ⟨90, 3, fun s =>
  if s = 1 then some ⟨2, 2⟩ else if s = 2 then some ⟨5, 5⟩ else none,
  fun s => if s = 1 ∨ s = 2 then Slot.ofValue (encodeWord word) else .empty⟩
private def packets : List ValueCell := SourceEval.Maximum.inputPackets
  (.shared ⟨2, []⟩) (.shared ⟨2, []⟩) word word

-- Both query references alias the first caller-owned tree. The complete caller
-- still retains both trees. Only the returned witness's two new Boxes survive;
-- every new table owner and symbolic stack root must be retired.
#eval show IO Unit from do
  match Recursive.original 128 17 world (List.range 6) [parent] .maximum packets with
  | none => throw (IO.userError "aliased public maximum failed")
  | some (final, packet, cost) =>
    match packet.2 with
    | .node .optional 1 [.node .embedding 0 [found, .number 1]] =>
      unless found == encodeWord word do throw (IO.userError "wrong maximum witness")
    | _ => throw (IO.userError "wrong maximum result or score")
    unless cost.work.steps == 2704 && cost.solverCalls == 5 do
      throw (IO.userError "wrong public maximum complete cost")
    unless final.memory.take 6 == world.memory && (List.range 6).all final.live do
      throw (IO.userError "public maximum changed retained caller cells")
    match traceResources final.memory packet.1 (Slot.ofValue packet.2) with
    | none => throw (IO.userError "public output resource readback failed")
    | some output =>
      unless output.owners.length == 2 && output.owners.all (fun a => decide (6 ≤ a)) do
        throw (IO.userError "public witness owners are not exactly two fresh Boxes")
      let completeOwners := output.owners ++ parent.owners final
      unless decide completeOwners.Nodup do throw (IO.userError "duplicate public/caller Box owner")
      unless completeOwners.all (fun a => decide (final.classes a = some .box) && final.live a) do
        throw (IO.userError "public/caller owner is not a live Box")
      unless (List.range final.memory.length).all (fun a =>
          if decide (final.classes a = some .box) && final.live a then decide (a ∈ completeOwners) else true) do
        throw (IO.userError "public maximum leaked a table Box")
      unless (List.range final.memory.length).all (fun a => final.live a == decide (a < 6 ∨ a ∈ output.owners)) do
        throw (IO.userError "public maximum left table or stack storage live")
    match SourceEval.run SourceEval.Certificate.original.body 17 .maximum (packets.map Prod.snd) with
    | none => throw (IO.userError "public pure source failed")
    | some (value, sourceCost) =>
      unless value == packet.2 && decide (sourceCost = cost) do
        throw (IO.userError "public source/addressed value or complete cost mismatch")
    IO.println "aliased public maximum: 2704 steps, 5 solver calls; table and stack cleanup checked"

end SourceMaximumExecutionTests
