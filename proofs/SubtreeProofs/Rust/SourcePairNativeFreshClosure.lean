module

public import SubtreeProofs.Rust.SourcePairSuccessfulTotality
public import SubtreeProofs.Rust.SourceTailFailureTotality
public import SubtreeProofs.Rust.SourceSubtotalOverflowTotality
public import SubtreeProofs.Rust.SourceRootOverflowTotality
public import SubtreeProofs.Rust.SourceLeftFailureTotality
public import SubtreeProofs.Rust.SourceRightFailureTotality
public import SubtreeProofs.Rust.SourceEvalTotal

/-! Close the pair/pair native calling contract from its four strictly smaller
fresh contracts. Independent functional evaluations select the branches; every
addressed parent run is constructed by its checked source-path theorem. -/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem pair_native_total_fresh (lh lt rh rt : BalancedWord)
    (headsTotal : NativeTotalFresh lh rh) (tailsTotal : NativeTotalFresh lt rt)
    (leftTotal : NativeTotalFresh (OrderedSolver.appendWord lh lt) (.Pair rh rt))
    (rightTotal : NativeTotalFresh (.Pair lh lt) (OrderedSolver.appendWord rh rt)) :
    NativeTotalFresh (.Pair lh lt) (.Pair rh rt) := by
  intro world callers previous guards hw hc view table leftCell rightCell tableCell leftRead rightRead tableRead
    owners external input frame coverage protectedReads
  cases found : MemoizedOrderedSolver.findResult table (.Pair lh lt) (.Pair rh rt) with
  | some witness =>
    obtain ⟨fuel, budget, final, packet, lookupCost, value, _, native, readable, wf, kept, resources, fresh, stable⟩ :=
      cache_hit_total_fresh hw hc view (.Pair lh lt) (.Pair rh rt) table leftCell rightCell tableCell
        leftRead rightRead tableRead input frame coverage protectedReads witness found
    exact ⟨fuel, budget, final, packet, some witness, table, hitRunCost lookupCost,
      value, native, readable, wf, kept, resources, fresh, stable⟩
  | none =>
    obtain ⟨_, heads, afterHeads, _, evaluatedHeads⟩ := evaluate_total lh rh table
    cases heads with
    | none =>
      obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
        head_failure_total_fresh hw hc view lh lt rh rt table afterHeads leftCell rightCell tableCell
          leftRead rightRead tableRead input frame coverage protectedReads found headsTotal.total evaluatedHeads.native
      exact ⟨fuel, budget, final, packet, none, afterHeads, cost, value, evaluated.native,
        readable, wf, kept, resources, fresh, stable⟩
    | some heads =>
      obtain ⟨_, tails, afterTails, _, evaluatedTails⟩ := evaluate_total lt rt afterHeads
      cases tails with
      | none =>
        obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
          tail_failure_total_fresh hw hc view lh lt rh rt table afterHeads afterTails heads leftCell rightCell tableCell
            leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
            evaluatedHeads.native evaluatedTails.native
        exact ⟨fuel, budget, final, packet, none, afterTails, cost, value, evaluated.native,
          readable, wf, kept, resources, fresh, stable⟩
      | some tails =>
        cases subtotalEq : Aeneas.Std.U32.checked_add heads.edges tails.edges with
        | none =>
          obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
            subtotal_overflow_total_fresh hw hc view lh lt rh rt table afterHeads afterTails heads tails
              leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
              evaluatedHeads.native evaluatedTails.native subtotalEq
          exact ⟨fuel, budget, final, packet, none, afterTails, cost, value, evaluated.native,
            readable, wf, kept, resources, fresh, stable⟩
        | some subtotal =>
          cases rootEq : Aeneas.Std.U32.checked_add subtotal 1#u32 with
          | none =>
            obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
              root_overflow_total_fresh hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal
                leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
                evaluatedHeads.native evaluatedTails.native subtotalEq rootEq
            exact ⟨fuel, budget, final, packet, none, afterTails, cost, value, evaluated.native,
              readable, wf, kept, resources, fresh, stable⟩
          | some total =>
            obtain ⟨_, leftWitness, afterLeft, _, evaluatedLeft⟩ :=
              evaluate_total (OrderedSolver.appendWord lh lt) (.Pair rh rt) afterTails
            cases leftWitness with
            | none =>
              obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
                left_failure_total_fresh hw hc view lh lt rh rt table afterHeads afterTails afterLeft heads tails subtotal total
                  leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
                  evaluatedHeads.native evaluatedTails.native subtotalEq rootEq leftTotal evaluatedLeft.native
              exact ⟨fuel, budget, final, packet, none, afterLeft, cost, value, evaluated.native,
                readable, wf, kept, resources, fresh, stable⟩
            | some leftWitness =>
              obtain ⟨_, rightWitness, afterRight, _, evaluatedRight⟩ :=
                evaluate_total (.Pair lh lt) (OrderedSolver.appendWord rh rt) afterLeft
              cases rightWitness with
              | none =>
                obtain ⟨fuel, budget, final, packet, cost, value, readable, wf, kept, resources, evaluated, fresh, stable⟩ :=
                  right_failure_total_fresh hw hc view lh lt rh rt table afterHeads afterTails afterRight heads tails subtotal total
                    leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
                    evaluatedHeads.native evaluatedTails.native subtotalEq rootEq leftTotal leftWitness afterLeft evaluatedLeft.native
                    rightTotal evaluatedRight.native
                exact ⟨fuel, budget, final, packet, none, afterRight, cost, value, evaluated.native,
                  readable, wf, kept, resources, fresh, stable⟩
              | some rightWitness =>
                obtain ⟨fuel, budget, final, packet, cost, value, native, readable, wf, kept, resources, _, fresh, stable⟩ :=
                  pair_successful_total_fresh hw hc view lh lt rh rt table afterHeads afterTails heads tails subtotal total
                    leftCell rightCell tableCell leftRead rightRead tableRead input frame coverage protectedReads found headsTotal tailsTotal
                    evaluatedHeads.native evaluatedTails.native subtotalEq rootEq leftTotal leftWitness afterLeft evaluatedLeft.native
                    rightTotal rightWitness afterRight evaluatedRight.native
                exact ⟨fuel, budget, final, packet, some (selectedWitness (matchedWitness heads tails total) leftWitness rightWitness),
                  .Entry ⟨.Pair lh lt, .Pair rh rt, selectedWitness (matchedWitness heads tails total) leftWitness rightWitness⟩ afterRight,
                  cost, value, native, readable, wf, kept, resources, fresh, stable⟩

end SubtreeProofs.Rust.SourceEval.Evaluator
