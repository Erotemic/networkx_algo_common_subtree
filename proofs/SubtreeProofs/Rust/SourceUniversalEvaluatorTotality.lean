module

public import SubtreeProofs.Rust.SourceEvaluatorNativeFreshTotality
public import SubtreeProofs.Rust.SourceEvalTypedRecursive

/-! Direct universal evaluator endpoint: actual checked dispatch exists and
agrees with both pure source execution and native Rust at the complete cost.
No smaller calling contract or successful parent execution remains a premise. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem native_evaluate_total_fresh {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (protectedReads : guards ⊆ previous.reads) :
    ∃ minimumFuel minimumBudget final packet result output cost,
      packet.2 = encodeOutput result output ∧
      memoized_common_embedding left right table = .ok (result, output) ∧
      Evaluation minimumFuel left right table result output cost ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell tableCell left right table) = some (final, packet, cost) := by
  obtain ⟨fuel, budget, final, packet, result, output, cost, value, native, readable, wf, kept, owned, fresh, stable⟩ :=
    native_total_fresh left right hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead
      input frame covered protectedReads
  have inputsReadable : ∀ packet ∈ inputPackets leftCell rightCell tableCell left right table,
      Readable world.memory world.live packet.1 packet.2 := by
    intro packet member
    simp only [inputPackets, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    · exact leftRead
    · exact rightRead
    · exact tableRead
  have alive : AliveOn world.live guards := fun address member => view.alive address (protectedReads member)
  obtain ⟨foundResult, foundOutput, _, refinedNative, evaluated, _, _, _⟩ :=
    Recursive.original_evaluate_typed_refines budget fuel hw hc inputsReadable alive left right table
      (by simp [inputPackets]) (stable fuel budget (by rfl) (by rfl))
  have fields := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans refinedNative))
  have resultEq : foundResult = result := fields.1.symm
  have outputEq : foundOutput = output := fields.2.symm
  subst foundResult
  subst foundOutput
  exact ⟨fuel, budget, final, packet, result, output, cost, value, native, evaluated, readable, wf, kept, owned, fresh, stable⟩

theorem native_evaluate_total_consistent {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat}
    (hw : world.WellFormed) (hc : ∀ caller ∈ callers, caller.Valid world) (view : Callers world callers previous)
    (left right : BalancedWord) (table : MemoTable) (leftCell rightCell tableCell : Cell)
    (leftRead : Readable world.memory world.live leftCell (.reference (encodeWord left)))
    (rightRead : Readable world.memory world.live rightCell (.reference (encodeWord right)))
    (tableRead : Readable world.memory world.live tableCell (encodeTable table))
    {owners external : List Nat}
    (input : FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners)
    (frame : OwnerFrame world (owners ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (owners ++ (callerOwners world callers ++ external)))
    (protectedReads : guards ⊆ previous.reads)
    (sound : MemoizedOrderedSolver.TableSound table)
    (leftBound : (OrderedSolver.toDyck left).semilength < 2^32)
    (rightBound : (OrderedSolver.toDyck right).semilength < 2^32) :
    ∃ minimumFuel minimumBudget final packet witness output cost,
      packet.2 = encodeOutput (some witness) output ∧
      memoized_common_embedding left right table = .ok (some witness, output) ∧
      Evaluation minimumFuel left right table (some witness) output cost ∧
      MemoizedOrderedSolver.Consistent left right witness ∧ MemoizedOrderedSolver.TableSound output ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate
          (inputPackets leftCell rightCell tableCell left right table) = some (final, packet, cost) := by
  obtain ⟨fuel, budget, final, packet, result, output, cost, value, native, evaluated, readable, wf, kept, owned, fresh, stable⟩ :=
    native_evaluate_total_fresh hw hc view left right table leftCell rightCell tableCell
      leftRead rightRead tableRead input frame covered protectedReads
  obtain ⟨witness, expected, expectedRun, consistent, outputSound, _⟩ :=
    MemoizedOrderedSolver.memoized_common_embedding_refines left right table sound leftBound rightBound
  have fields := Prod.mk.inj (Aeneas.Std.Result.ok_injective (native.symm.trans expectedRun))
  have resultEq : result = some witness := fields.1
  have outputEq : expected = output := fields.2.symm
  subst result
  subst expected
  exact ⟨fuel, budget, final, packet, witness, output, cost, value, native, evaluated, consistent, outputSound,
    readable, wf, kept, owned, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
