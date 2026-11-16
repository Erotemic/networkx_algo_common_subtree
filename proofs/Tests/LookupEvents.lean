import SubtreeProofs.Rust.LookupEvents

/-! Campaign G1 discriminator cases for the bounded packet model. These check
the cost semantics as well as results; they do not certify Rust instrumentation. -/

namespace LookupEventTests

open verified_ordered_core SubtreeProofs.Rust.LookupEvents

private def e : BalancedWord := .Empty
private def one : BalancedWord := .Pair e e
private def two : BalancedWord := .Pair one e
private def result (w : BalancedWord) : CommonEmbedding := ⟨w, 0#u32⟩
private def entry (l r w : BalancedWord) : MemoEntry := ⟨l, r, result w⟩

-- Empty table includes the terminal visit, with no comparisons or copies.
example : (lookup .Empty two two).2 = ⟨1, 0, 0, 0, 0⟩ := rfl

-- Missing left key: no right comparison, including when that key is large.
example : lookup (.Entry (entry one two e) .Empty) e two =
    (none, ⟨2, 1, 0, 0, 0⟩) := rfl

-- Missing right key: both the left hit and the right mismatch are charged.
example : lookup (.Entry (entry one two e) .Empty) one e =
    (none, ⟨2, 4, 0, 0, 0⟩) := rfl

-- First hit returns before a suffix scan and copies the whole cached witness.
example : lookup (.Entry (entry one one two) (.Entry (entry one one e) .Empty)) one one =
    (some (result two), ⟨1, 6, 5, 4, 1⟩) := rfl

-- Last hit visits both records, but does not visit the terminal Empty.
example : lookup (.Entry (entry e two e) (.Entry (entry one one two) .Empty)) one one =
    (some (result two), ⟨2, 7, 5, 4, 1⟩) := rfl

-- Duplicate keys deliberately have first-hit semantics, with different results.
example : (lookup (.Entry (entry e e one) (.Entry (entry e e two) .Empty)) e e).1 =
    some (result one) := rfl

-- The differing heads prevent traversal of the two large tails.
example : SubtreeProofs.Rust.LookupEvents.compare (.Pair e two) (.Pair one two) = (false, 2) := rfl

-- Equal structural keys traverse all five constructors, not one key operation.
example : SubtreeProofs.Rust.LookupEvents.compare two two = (true, 5) := rfl

-- An unsound zero-size key can return a larger witness: copy cost needs a
-- soundness premise before it can be bounded in query sizes.
example : lookup (.Entry (entry e e two) .Empty) e e =
    (some (result two), ⟨1, 2, 5, 4, 1⟩) := rfl

-- Same answer, twice the events. The old one-visit budget now fails.
example : (lookupTwice (.Entry (entry e e two) .Empty) e e).2 =
    ⟨2, 4, 10, 8, 2⟩ := rfl

end LookupEventTests
