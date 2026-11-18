module

public import SubtreeProofs.Rust.SourcePairLeftScopeEntry

/-! The unchanged successful-left/right-contraction source region, including
its actual optional-result switch and failure/finish continuations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rightContractionCases : Code := .switch (.discriminant (.local 88)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none .done finish rightFailure

def rightActions : List Action :=
  [.storageLive 82, .assign 82 (.use (.move (.field (.local 74) (some 1) 0))),
   .assign 81 (.use (.move (.local 82))), .drop 82, .storageDead 82, .fakeRead (.local 81),
   .storageLive 85, .storageLive 86, .assign 86 (.address (.deref (.deref (.local 29)))),
   .storageLive 87, .assign 87 (.address (.deref (.deref (.local 30)))),
   .call .concatenate [.move (.local 86), .move (.local 87)] 85,
   .storageDead 87, .storageDead 86, .fakeRead (.local 85),
   .storageLive 90, .storageLive 91, .assign 91 (.address (.deref (.local 1))),
   .storageLive 92, .storageLive 93, .assign 93 (.address (.local 85)),
   .assign 92 (.address (.deref (.local 93))),
   .storageLive 94, .assign 94 (.use (.move (.local 75))),
   .call .evaluate [.move (.local 91), .move (.local 92), .move (.local 94)] 90,
   .storageDead 94, .storageDead 92, .storageDead 91,
   .storageLive 88, .assign 88 (.use (.move (.field (.local 90) none 0))),
   .storageLive 89, .assign 89 (.use (.move (.field (.local 90) none 1))),
   .drop 90, .storageDead 93, .storageDead 90, .storageLive 95]

def rightCode (index : Nat) : Code := (rightActions.drop index).foldr Control.Tree.step rightContractionCases

theorem contractRight_actions : contractRight = rightActions.foldr Control.Tree.step rightContractionCases := rfl

end SubtreeProofs.Rust.SourceEval.Evaluator
