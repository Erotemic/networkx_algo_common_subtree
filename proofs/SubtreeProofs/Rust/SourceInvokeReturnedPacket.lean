module

public import SubtreeProofs.Rust.SourceEvalCallingEntry

/-! Successful invocation retains the packet of its actual returned body and
performs the actual close on that packet. Closure leaves memory bytes intact. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap SourceEval.Addressed

theorem close_memory {world final : World} {active : Activation} {callers : List Activation}
    {guards : List Nat} {packet : ValueCell} (run : close world active callers guards packet = some final) :
    final.memory = world.memory := by
  simp only [close, bind, Option.bind_eq_some_iff] at run
  obtain ⟨current, scanned, suspended, callerScan, used, traced, last⟩ := run
  split at last
  next accepted => cases last; rfl
  next => cases last

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem invoke_returned_close {callee : Derived.Callees} {decl : TypeReader.Definition}
    {world entered middle final : World} {active after : Activation} {callers : List Activation}
    {guards : List Nat} {packets : List ValueCell} {returned packet : ValueCell} {work cost : Cost}
    (entryRun : enter world world.memory.length decl.source.localCount packets = some (entered, active))
    (bodyRun : exec callee callers decl.source.code entered active = some (.returned middle after returned, work))
    (run : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    packet = returned ∧ close middle after callers guards returned = some final ∧ cost = (Cost.entry decl.source.function).plus work := by
  unfold invoke at run
  split at run
  next arity =>
    simp only [entryRun, bind, Option.bind, bodyRun] at run
    change (do let closed ← close middle after callers guards returned
               some (closed, returned, (Cost.entry decl.source.function).plus work)) = some (final, packet, cost) at run
    simp only [bind, Option.bind_eq_some_iff] at run
    obtain ⟨closed, closeRun, same⟩ := run
    cases same
    exact ⟨rfl, closeRun, rfl⟩
  next => cases run

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
