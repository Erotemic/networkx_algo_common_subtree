import SubtreeProofs.Rust.LookupSourceMutation

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace LookupSourceTests

open verified_ordered_core SubtreeProofs.Rust.LookupSource

private def e : BalancedWord := .Empty
private def one : BalancedWord := .Pair e e
private def two : BalancedWord := .Pair one e
private def result (word : BalancedWord) : CommonEmbedding := ⟨word, 7#u32⟩
private def entry (l r word : BalancedWord) : MemoEntry := ⟨l, r, result word⟩

private def observe (table : MemoTable) (left right : BalancedWord) :=
  (run Program.body (lookupDepth table left right) .lookup
    [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)]).map
      (fun pair => (pair.1, pair.2.events))

-- Empty input, including the source's terminal table visit.
example : observe .Empty two two = some (encodeOption none, ⟨1, 0, 0, 0, 0⟩) := rfl

-- A left-key mismatch skips the right-key call entirely.
example : observe (.Entry (entry one two e) .Empty) e two =
    some (encodeOption none, ⟨2, 1, 0, 0, 0⟩) := rfl

-- The left hit and right mismatch both execute in this case.
example : observe (.Entry (entry one two e) .Empty) one e =
    some (encodeOption none, ⟨2, 4, 0, 0, 0⟩) := rfl

-- First hit ignores the suffix; the owned result and nonzero u32 payload survive.
example : observe (.Entry (entry one one two) (.Entry (entry one one e) .Empty)) one one =
    some (encodeOption (some (result two)), ⟨1, 6, 5, 4, 1⟩) := rfl

-- Last hit visits both records without the terminal empty visit.
example : observe (.Entry (entry e two e) (.Entry (entry one one two) .Empty)) one one =
    some (encodeOption (some (result two)), ⟨2, 7, 5, 4, 1⟩) := rfl

-- Duplicate keys have first-hit, rather than finite-map, semantics.
example : observe (.Entry (entry e e one) (.Entry (entry e e two) .Empty)) e e =
    some (encodeOption (some (result one)), ⟨1, 2, 3, 2, 1⟩) := rfl

-- An early head mismatch does not scan either tail or compare the right key.
example : observe (.Entry (entry (.Pair one two) two e) .Empty) (.Pair e two) two =
    some (encodeOption none, ⟨2, 2, 0, 0, 0⟩) := rfl

-- Equality traverses all structural constructors, not a unit key comparison.
example : observe (.Entry (entry two two e) .Empty) two two =
    some (encodeOption (some (result e)), ⟨1, 10, 1, 0, 1⟩) := rfl

-- Unsound caches can return witnesses larger than the query: copy work remains.
example : observe (.Entry (entry e e two) .Empty) e e =
    some (encodeOption (some (result two)), ⟨1, 2, 5, 4, 1⟩) := rfl

-- Unsupported live destruction and free owned structural copies fail explicitly.
example : evalAction (fun (_ : Function) _ => none) (initialEnv [encodeWord one]) (.dropMoved 1) = none := rfl
example : evalOperand (initialEnv [encodeWord one]) (.copy (.local 1)) = none := rfl

end LookupSourceTests
