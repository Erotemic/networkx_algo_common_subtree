module

public import SubtreeProofs.Rust.LookupFramePrimitives
public import SubtreeProofs.Rust.MemoSourceRefinement

/-! Conservative owner profiles for memo helpers. Insertion may consume an
owned table; shared keys/results remain non-owning. A true flag allows plain
values as well, without treating a potentially owned value as plain. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

def flagsFit : List Bool → List Bool → Bool
  | [], [] => true
  | actual :: rest, expected :: tail => (!actual || expected) && flagsFit rest tail
  | _, _ => false

theorem FieldsMatch.widen {actual expected : List Bool} {cells : List Cell}
    (hm : FieldsMatch actual cells) (hf : flagsFit actual expected = true) : FieldsMatch expected cells := by
  induction actual generalizing expected cells with
  | nil => cases cells with
    | cons _ _ => cases hm
    | nil => cases expected with
      | nil => trivial
      | cons _ _ => cases hf
  | cons flag flags ih => cases cells with
    | nil => cases hm
    | cons cell cells => cases expected with
      | nil => cases hf
      | cons other others =>
        have hh := Bool.and_eq_true_iff.mp hf
        refine ⟨?_, ih hm.2 hh.2⟩
        cases other with
        | true => trivial
        | false =>
          cases flag with
          | false => exact hm.1
          | true => cases hh.1

end SubtreeProofs.Rust.LookupSource.Heap.Frame

namespace SubtreeProofs.Rust.MemoSource.Frame

open LookupSource LookupSource.Heap LookupSource.Heap.Frame

def inputFlags : Function → List Bool
  | .copyWord | .copyResult => [false]
  | .concatenate => [false, false]
  | .insert => [true, false, false, false]
  | .boxNew => [true]

def outputFlag (_ : Function) : Bool := true

def ArgsMatch (function : Function) (cells : List Cell) : Prop :=
  cells.length = arity function ∧ (function = .boxNew ∨ FieldsMatch (inputFlags function) cells)

def callProfile (function : Function) (flags : List Bool) : Bool :=
  flags.length == arity function && (function == .boxNew || flagsFit flags (inputFlags function))

theorem profile_sound {function : Function} {flags : List Bool} {cells : List Cell}
    (hm : FieldsMatch flags cells) (hc : callProfile function flags = true) : ArgsMatch function cells := by
  have hh := Bool.and_eq_true_iff.mp hc
  refine ⟨hm.length.trans (by simpa using hh.1), ?_⟩
  by_cases hb : function = .boxNew
  · exact Or.inl hb
  · exact Or.inr (hm.widen (by simpa [hb] using hh.2))

theorem input_length (function : Function) : (inputFlags function).length = arity function := by
  cases function <;> rfl

end SubtreeProofs.Rust.MemoSource.Frame
