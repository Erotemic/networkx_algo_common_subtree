module

public import SubtreeProofs.Complexity.EditDistance.Memo
public import SubtreeProofs.Complexity.Memo.ProductCache

/-! The same independent edit-distance problem and generic combinatorial proof
with two executable cache representations. Setup initializes actual storage;
dense addressing includes its two arithmetic encoding units per operation.
Complete representation work envelopes and input/source realization remain
separate from these value and request-count contracts. -/

@[expose] public section

namespace SubtreeProofs.Complexity.EditDistance

variable {Symbol : Type} [DecidableEq Symbol]

def runList (left right : List Symbol) (roots : List (Key left right)) :
    Nat × EStateM.Result Unit (Memo.EvalState (Key left right) (List (Key left right × Nat))) (List Nat) :=
  let initial := (Memo.ListCache.buildEmpty : List (Key left right × Nat) × Nat)
  (initial.2, Memo.evalRoots Memo.ListCache.ops (body left right)
    (left.length + right.length + 1) roots ⟨initial.1, []⟩)

def runDense (left right : List Symbol) (roots : List (Key left right)) :
    Nat × EStateM.Result Unit (Memo.EvalState (Key left right) (Array (Option Nat))) (List Nat) :=
  let initial := Memo.DirectCache.buildEmpty Nat ((left.length + 1) * (right.length + 1))
  (initial.2, Memo.evalRoots (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat)
    (body left right) (left.length + right.length + 1) roots ⟨initial.1, []⟩)

theorem list_roots_spec (left right : List Symbol) (roots : List (Key left right)) :
    ∃ final, (runList left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant Memo.ListCache.ops (problem left right) [] final ∧
      (Memo.Event.completedKeys final.events).length ≤ (left.length + 1) * (right.length + 1) ∧
      Memo.Event.calls final.events ≤ roots.length +
        3 * ((left.length + 1) * (right.length + 1)) := by
  simpa [runList, Memo.ListCache.buildEmpty, Memo.ListCache.ops, Fintype.card_prod]
    using roots_spec left right Memo.ListCache.ops [] roots
      (Memo.ListCache.initial_valid) (Memo.ListCache.initial_sound (value left right))

theorem dense_roots_spec (left right : List Symbol) (roots : List (Key left right)) :
    ∃ final, (runDense left right roots).2 = .ok (roots.map (value left right)) final ∧
      Memo.TraceInvariant (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat)
        (problem left right) (Memo.DirectCache.buildEmpty Nat ((left.length + 1) * (right.length + 1))).1
        final ∧
      (Memo.Event.completedKeys final.events).length ≤ (left.length + 1) * (right.length + 1) ∧
      Memo.Event.calls final.events ≤ roots.length +
        3 * ((left.length + 1) * (right.length + 1)) := by
  simpa [runDense, Memo.DirectCache.productOps, Memo.DirectCache.ops,
      Memo.DirectCache.buildEmpty_empty, Fintype.card_prod]
    using roots_spec left right
      (Memo.DirectCache.productOps (left.length + 1) (right.length + 1) Nat)
      (Memo.DirectCache.buildEmpty Nat ((left.length + 1) * (right.length + 1))).1 roots
      (Memo.DirectCache.product_initial_valid _ _ Nat)
      (Memo.DirectCache.product_initial_sound _ _ Nat (value left right))

@[simp] theorem list_setup (left right : List Symbol) (roots : List (Key left right)) :
    (runList left right roots).1 = 1 := rfl

theorem dense_setup (left right : List Symbol) (roots : List (Key left right)) :
    (runDense left right roots).1 = (left.length + 1) * (right.length + 1) + 1 :=
  Memo.DirectCache.buildEmpty_work Nat _

end SubtreeProofs.Complexity.EditDistance
