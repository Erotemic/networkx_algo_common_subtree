module

public import SubtreeProofs.Rust.SourcePairScoreEntry
public import SubtreeProofs.Rust.SourceOriginalNumberAssign

/-! The actual twelve-instruction root-score prefix and its retained overflow,
contraction and cleanup continuations. Subtotal payload copying is scalar-only. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def rootScoreCases : Code := .switch (.discriminant (.local 59)) [(.variant .optional 0, 0), (.variant .optional 1, 1)] none rootOverflow contractLeft cleanupSubtotal

def rootScoreActions : List Action :=
  [.storageLive 55, .assign 55 (.use (.copy (.field (.local 52) (some 1) 0))),
   .assign 51 (.use (.copy (.local 55))), .storageDead 55, .fakeRead (.local 51), .storageDead 52,
   .storageLive 58, .storageLive 59, .storageLive 60, .assign 60 (.use (.copy (.local 51))),
   .call .checkedAdd [.move (.local 60), .number 1] 59, .storageDead 60]

def rootScoreCode (index : Nat) : Code := (rootScoreActions.drop index).foldr Control.Tree.step rootScoreCases

theorem addRoot_actions : addRoot = rootScoreActions.foldr Control.Tree.step rootScoreCases := rfl

theorem number_option_payload_read (number : Nat) :
    (Slot.ofValue (encodeNumberOption (some number))).read [.field (some 1) 0] = some (.number number) := by
  simp [encodeNumberOption, Slot.ofValue, ofFields, Slot.read, Slot.get, Slot.materialize]

theorem number_local_read (number : Nat) : Slot.read (.number number) [] = some (.number number) := by
  simp [Slot.read, Slot.get, Slot.materialize]

end SubtreeProofs.Rust.SourceEval.Evaluator
