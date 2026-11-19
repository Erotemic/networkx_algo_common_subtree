module

public import SubtreeProofs.Rust.SourceEvaluatorNativeTotal
public import SubtreeProofs.Rust.SourceEmptyOwnerProvenance

/-! A separate stronger induction contract bounds only the returned witness's
owners. Its empty-query bases include arbitrary typed warm-table hits, even
nonempty cached witnesses, and requested-key misses. The original NativeTotal
contract is unchanged and follows by projection. The universal instance is proved
separately in SourceEvaluatorNativeFreshTotality; these bases assume no instance. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def NativeTotalFresh (left right : BalancedWord) : Prop :=
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
      ResultOwnersAbove world.memory.length final.memory packet.1 ∧
      ∀ fuel budget, minimumFuel ≤ fuel → minimumBudget ≤ budget →
        Recursive.original budget fuel world guards callers .evaluate (inputPackets leftCell rightCell tableCell left right table) =
          some (final, packet, cost)


theorem NativeTotalFresh.total {left right : BalancedWord} (h : NativeTotalFresh left right) : NativeTotal left right := by
  intro world callers previous guards hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead
    owners external input frame coverage protectedReads
  obtain ⟨fuel, budget, final, packet, result, output, cost, value, native, readable, wf, kept, resources, _, stable⟩ :=
    h hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads
  exact ⟨fuel, budget, final, packet, result, output, cost, value, native, readable, wf, kept, resources, stable⟩

theorem native_empty_total_fresh (left right : BalancedWord) (empty : left = .Empty ∨ right = .Empty) : NativeTotalFresh left right := by
  intro world callers previous guards hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead owners external footprint frame coverage protectedReads
  cases found : MemoizedOrderedSolver.findResult table left right with
  | some result =>
    obtain ⟨fuel, budget, final, packet, lookupCost, value, _, native, readable, wf, kept, resources, fresh, stable⟩ :=
      cache_hit_total_fresh hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
        footprint frame coverage protectedReads result found
    exact ⟨fuel, budget, final, packet, some result, table, hitRunCost lookupCost, value, native, readable, wf, kept, resources, fresh, stable⟩
  | none =>
    obtain ⟨fuel, budget, final, packet, lookupCost, insertCost, value, _, _, native, readable, wf, kept, resources, fresh, stable⟩ :=
      empty_miss_total_fresh hw hc view left right table leftCell rightCell tableCell leftRead rightRead tableRead
        footprint frame coverage protectedReads empty found
    exact ⟨fuel, budget, final, packet, some emptyWitness, .Entry ⟨left, right, emptyWitness⟩ table,
      emptyRunCost left lookupCost insertCost, value, native, readable, wf, kept, resources, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
