module

public import SubtreeProofs.Rust.SourceEvalMachine

/-! Explicit score-choice control proposed for the actual source identity
check. Execution and source binding are proved in the accompanying modules. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource

def branch (winner : Nat) : Code :=
  .step (.storageDead 5) (.step (.storageDead 4)
    (.step (.assign 0 (.use (.move (.local winner)))) .done))

def body : Code :=
  .step (.storageLive 0) <|
  .step (.storageLive 3) <|
  .step (.storageLive 4) <|
  .step (.assign 4 (.use (.copy (.field (.local 1) none 1)))) <|
  .step (.storageLive 5) <|
  .step (.assign 5 (.use (.copy (.field (.local 2) none 1)))) <|
  .step (.assign 3 (.less (.move (.local 4)) (.move (.local 5)))) <|
  .switch (.value (.move 3)) [(.boolean false, 1)] (some 0) (branch 2) (branch 1) <|
  .step (.storageDead 3) <|
  .step (.drop 2) <|
  .step (.drop 1) <|
  .step (.storageDead 2) <|
  .step (.storageDead 1) .ret

end SubtreeProofs.Rust.SourceEval.Choice
