module

public import SubtreeProofs.Rust.SourceRecursiveBoxOrigin
public import SubtreeProofs.Rust.SourceOwnerRecursive
public import SubtreeProofs.Rust.SourceUniversalEvaluatorTotality

/-! An ownership-free typed input cannot acquire old caller/external Boxes in
its returned ownership packet. The cold evaluator therefore returns a wholly
fresh witness/table packet, including every Box in its actual updated table. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Recursive

open LookupSource Heap Partial Partial.Addressed Storage

theorem original_fresh_output_of_no_input_owners (budget fuel : Nat)
    {world final : World} {callers : List Activation} {guards : List Nat}
    {function : Function} {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    {previous : Resources} {external : List Nat}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : Derived.TypedReady world function packets) (view : Callers world callers previous)
    (alive : AliveOn world.live guards)
    (input : FieldsFootprint world.memory (packets.map Prod.fst) [])
    (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external))
    (run : original budget fuel world guards callers function packets = some (final, packet, cost)) :
    ∃ output, Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external)) ∧
      (∀ address ∈ output, world.memory.length ≤ address) ∧ Preserves world final previous.reads := by
  have kept := original_callers_preserved budget fuel hw hc hp hd view run
  have callerEq := view.owners_preserved (view.transport kept)
  obtain ⟨output, footprint, owned, coverage⟩ := original_owns budget fuel
    world guards callers function packets final packet cost [] external hw hc hp alive hd input
    (by simpa only [List.nil_append] using frame) (by simpa only [List.nil_append] using covered) run
  have origin := original_boxOrigin budget fuel world guards callers function packets final packet cost hw hc hp hd run
  refine ⟨output, footprint, owned, coverage, ?_, kept⟩
  apply origin.fresh_output covered
  rwa [callerEq]

end SubtreeProofs.Rust.SourceEval.Addressed.Recursive

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem native_evaluate_cold_total {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (leftCell rightCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    {external : List Nat}
    (frame : OwnerFrame world (callerOwners world callers ++ external))
    (covered : BoxCoverage world (callerOwners world callers ++ external))
    (protectedReads : guards ⊆ previous.reads) :
    ∃ minimumFuel minimumBudget final packet result output cost outputOwners,
      packet.2 = encodeOutput result output ∧
      memoized_common_embedding left right .Empty = .ok (result, output) ∧
      Evaluation minimumFuel left right .Empty result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧
      Preserves world final previous.reads ∧
      Footprint final.memory packet.1 outputOwners ∧
      OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external)) ∧
      (∀ address ∈ outputOwners, world.memory.length ≤ address) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell (.node .table 0 []) left right .Empty) = some (final, packet, cost) := by
  have leftOwned : Footprint world.memory leftCell [] := by
    obtain ⟨_, graph, _⟩ := leftRead
    cases graph with | shared pointer child => exact .shared _
  have rightOwned : Footprint world.memory rightCell [] := by
    obtain ⟨_, graph, _⟩ := rightRead
    cases graph with | shared pointer child => exact .shared _
  have input : FieldsFootprint world.memory [leftCell, rightCell, .node .table 0 []] [] :=
    .cons leftOwned (.cons rightOwned (.cons (.node .nil) .nil))
  have tableRead : Readable world.memory world.live (.node .table 0 []) (encodeTable .Empty) :=
    ⟨[], .node .nil, by simp [AliveOn]⟩
  obtain ⟨fuel, budget, final, packet, result, output, cost, value, native, evaluated, readable, wf, _, _, _, stable⟩ :=
    native_evaluate_total_fresh hw hc view left right .Empty leftCell rightCell (.node .table 0 [])
      leftRead rightRead tableRead input (by simpa using frame) (by simpa using covered) protectedReads
  have inputsReadable : ∀ packet ∈ inputPackets leftCell rightCell (.node .table 0 []) left right .Empty,
      Readable world.memory world.live packet.1 packet.2 := by
    intro packet member
    simp only [inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact leftRead
    · exact rightRead
    · exact tableRead
  have typed : Derived.TypedReady world .evaluate (inputPackets leftCell rightCell (.node .table 0 []) left right .Empty) := by
    refine ⟨Types.inputs .evaluate, Types.output .evaluate, ?_, ?_⟩
    · exact .cons (.shared (word_typed left)) (.cons (.shared (word_typed right)) (.cons (table_typed .Empty) .nil))
    · simp only [Types.callOutput, reduceCtorEq, ite_false, SourceTypes.sameList_refl, ite_true]
  obtain ⟨owners, footprint, owned, coverage, fresh, kept⟩ :=
    Recursive.original_fresh_output_of_no_input_owners budget fuel hw hc inputsReadable typed view
      (fun address member => view.alive address (protectedReads member)) input frame covered
      (stable fuel budget (by rfl) (by rfl))
  exact ⟨fuel, budget, final, packet, result, output, cost, owners, value, native, evaluated, readable, wf,
    kept, footprint, owned, coverage, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
