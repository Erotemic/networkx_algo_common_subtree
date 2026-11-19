module

public import SubtreeProofs.Rust.SourcePairRootScoreEntry

/-! The actual successful-root-score/matched-witness and left-contraction
instructions, retaining the real recursive-result switch and cleanup joins. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def matchedCases : Code := .switch (.discriminant (.local 74)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none leftFailure contractRight cleanupLeft

def matchedActions : List Action :=
  [.storageLive 61, .assign 61 (.use (.copy (.field (.local 59) (some 1) 0))),
   .assign 58 (.use (.copy (.local 61))), .storageDead 61, .fakeRead (.local 58), .storageDead 59,
   .storageLive 64, .storageLive 65, .storageLive 66, .storageLive 67,
   .assign 67 (.use (.move (.field (.local 37) none 0))),
   .call .boxNew [.move (.local 67)] 66, .storageDead 67,
   .storageLive 68, .storageLive 69, .assign 69 (.use (.move (.field (.local 47) none 0))),
   .call .boxNew [.move (.local 69)] 68, .storageDead 69,
   .assign 65 (.aggregate .word 1 [.move (.local 66), .move (.local 68)]),
   .drop 68, .storageDead 68, .drop 66, .storageDead 66,
   .storageLive 70, .assign 70 (.use (.copy (.local 58))),
   .assign 64 (.aggregate .embedding 0 [.move (.local 65), .move (.local 70)]),
   .storageDead 70, .drop 65, .storageDead 65, .fakeRead (.local 64),
   .storageLive 71, .storageLive 72, .assign 72 (.address (.deref (.deref (.local 27)))),
   .storageLive 73, .assign 73 (.address (.deref (.deref (.local 28)))),
   .call .concatenate [.move (.local 72), .move (.local 73)] 71,
   .storageDead 73, .storageDead 72, .fakeRead (.local 71),
   .storageLive 76, .storageLive 77, .storageLive 78, .assign 78 (.address (.local 71)),
   .assign 77 (.address (.deref (.local 78))), .storageLive 79, .assign 79 (.address (.deref (.local 2))),
   .storageLive 80, .assign 80 (.use (.move (.local 42))),
   .call .evaluate [.move (.local 77), .move (.local 79), .move (.local 80)] 76,
   .storageDead 80, .storageDead 79, .storageDead 77,
   .storageLive 74, .assign 74 (.use (.move (.field (.local 76) none 0))),
   .storageLive 75, .assign 75 (.use (.move (.field (.local 76) none 1))),
   .drop 76, .storageDead 78, .storageDead 76, .storageLive 81]

def matchedCode (index : Nat) : Code := (matchedActions.drop index).foldr Control.Tree.step matchedCases

theorem contractLeft_actions : contractLeft = matchedActions.foldr Control.Tree.step matchedCases := rfl

end SubtreeProofs.Rust.SourceEval.Evaluator
