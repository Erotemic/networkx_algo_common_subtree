module

public import SubtreeProofs.Rust.SourceLeftFailureCleanup
public import SubtreeProofs.Rust.SourcePairRightStorageEntry

/-! Actual right-failure join: failure packing followed by right query/result
retirement and the held left-witness drop. Root81 remains for outer cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rightFailureCleanupActions : List Action :=
  [.storageDead 95, .drop 89, .storageDead 89, .drop 88, .storageDead 88,
    .drop 85, .storageDead 85, .drop 81]

def rightFailureActions : List Action := failurePackActions 89 97 98 ++ rightFailureCleanupActions

theorem rightFailure_actions : rightFailure = rightFailureActions.foldr Control.Tree.step .done := rfl

end SubtreeProofs.Rust.SourceEval.Evaluator
