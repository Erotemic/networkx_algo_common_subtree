module

public import SubtreeProofs.Rust.OrderedSolver
public import SubtreeProofs.Paper2004.IndexedWord
import Mathlib.Tactic

/-! # Actual indexed Rust words and identity-preserving structural helpers -/

@[expose] public section

open Aeneas Aeneas.Std Result
open verified_ordered_core

namespace SubtreeProofs.Rust.IndexedOrderedSolver


/-- Interpret actual machine pair identities in the independent indexed model. -/
def model : indexed.IndexedWord → Paper2004.IndexedWord.Word
  | .Empty => .nil
  | .Pair index head tail => .node index.val (model head) (model tail)

def appendWord : indexed.IndexedWord → indexed.IndexedWord → indexed.IndexedWord
  | .Empty,right => right
  | .Pair index head tail,right => .Pair index head (appendWord tail right)

@[simp] theorem model_appendWord (left right : indexed.IndexedWord) :
    model (appendWord left right) = Paper2004.IndexedWord.append (model left) (model right) := by
  induction left with
  | Empty => rfl
  | Pair index head tail _ ih => simp only [appendWord,model,Paper2004.IndexedWord.append,ih]

/-- Actual copying preserves every identity and the complete nesting structure. -/
theorem copy_indexed_correct (word : indexed.IndexedWord) : indexed.copy_indexed word = .ok word := by
  induction word with
  | Empty => rw [indexed.copy_indexed]
  | Pair index head tail ihHead ihTail =>
    rw [indexed.copy_indexed,ihHead,bind_ok,ihTail,bind_ok]

/-- Actual concatenation preserves both original identity lists and splicing. -/
theorem append_indexed_correct (left right : indexed.IndexedWord) :
    indexed.append_indexed left right = .ok (appendWord left right) := by
  induction left with
  | Empty => rw [indexed.append_indexed,copy_indexed_correct]; rfl
  | Pair index head tail _ ih =>
    rw [indexed.append_indexed,copy_indexed_correct,bind_ok,ih,bind_ok]
    rfl

end SubtreeProofs.Rust.IndexedOrderedSolver

end
