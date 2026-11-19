module

public import SubtreeProofs.Rust.ScoreModel.Types

/-! Maintained definitions for exactly the four opaque Rust score primitives.
These are total rational operations, not assumptions about native IEEE-754. -/

@[expose] public section

namespace arithmetic

def zero : Aeneas.Std.Result Score := .ok 0

def add (left right : Score) : Aeneas.Std.Result Score := .ok (left + right)

def positive (value : Score) : Aeneas.Std.Result Bool := .ok (decide (0 < value))

def greater (left right : Score) : Aeneas.Std.Result Bool := .ok (decide (right < left))

end arithmetic
