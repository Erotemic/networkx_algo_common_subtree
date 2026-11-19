module

public import SubtreeProofs.Rust.SourceEmptyTotality
public import SubtreeProofs.Rust.SourceCacheHitTotality

/-! The universal native calling contract used as the induction hypothesis for
smaller evaluator requests. Empty inputs satisfy the complete contract, allowing
arbitrary warm tables and legal query/table/caller aliases. SourceEvaluatorNativeFreshTotality proves the universal projection separately;
this contract and its empty bases assume no global instance. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def NativeTotal (left right : BalancedWord) : Prop :=
  ∀ {world : World} {callers : List Activation} {previous : Resources} {guards : List Nat},
    world.WellFormed → (∀ caller ∈ callers, caller.Valid world) → Callers world callers previous →
    ∀ (table : MemoTable) (leftCell rightCell tableCell : Cell),
    Readable world.memory world.live leftCell (.reference (encodeWord left)) →
    Readable world.memory world.live rightCell (.reference (encodeWord right)) →
    Readable world.memory world.live tableCell (encodeTable table) →
    ∀ {owners external : List Nat}, FieldsFootprint world.memory [leftCell, rightCell, tableCell] owners →
    OwnerFrame world (owners ++ (callerOwners world callers ++ external)) →
    BoxCoverage world (owners ++ (callerOwners world callers ++ external)) → guards ⊆ previous.reads →
    ∃ (minimumFuel minimumBudget : Nat) (final : World) (packet : ValueCell)
      (result : Option CommonEmbedding) (output : MemoTable) (cost : Cost),
      packet.2 = encodeOutput result output ∧ memoized_common_embedding left right table = .ok (result, output) ∧
      Readable final.memory final.live packet.1 packet.2 ∧ final.WellFormed ∧ Preserves world final guards ∧
      (∃ outputOwners, Footprint final.memory packet.1 outputOwners ∧
        OwnerFrame final (outputOwners ++ (callerOwners final callers ++ external)) ∧
        BoxCoverage final (outputOwners ++ (callerOwners final callers ++ external))) ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate (inputPackets leftCell rightCell tableCell left right table) =
          some (final, packet, cost)

theorem native_empty_total (left right : BalancedWord) (empty : left = .Empty ∨ right = .Empty) : NativeTotal left right := by
  intro world callers previous guards hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead owners external footprint frame coverage protectedReads
  cases found : MemoizedOrderedSolver.findResult table left right with
  | some result =>
    obtain ⟨fuel, budget, final, packet, lookupCost, value, _, native, readable, wf, kept, resources, stable⟩ :=
      cache_hit_total hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
        footprint frame coverage protectedReads result found
    exact ⟨fuel, budget, final, packet, some result, table, hitRunCost lookupCost, value, native, readable, wf, kept, resources, stable⟩
  | none =>
    obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, _, _, native, readable, wf, kept, resources, stable⟩ :=
      empty_miss_total hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
        footprint frame coverage protectedReads empty found
    exact ⟨fuel, budget, final, packet, some emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table,
      emptyRunCost left lookupCost insertCost, value, native, readable, wf, kept, resources, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
