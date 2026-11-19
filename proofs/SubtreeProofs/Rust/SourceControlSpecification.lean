module

public import SubtreeProofs.Rust.LookupSourceControl

/-! A successful source dispatch satisfies every postcondition shared by its
successful arms. Routing and branch costs remain in the existing interpreter. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Control

theorem selectSource_spec {α : Type} (actual : Key) (branches : List (Key × Nat)) (fallback : Option Nat)
    {left right : Option α} {P : α → Prop}
    (hl : ∀ value, left = some value → P value) (hr : ∀ value, right = some value → P value)
    {value : α} (he : selectSource actual branches fallback (fun _ => left) (fun _ => right) = some value) :
    P value := by
  simp only [selectSource] at he
  cases hi : selectIndex actual branches fallback with
  | none => simp [hi] at he
  | some index =>
    cases index with
    | zero => exact hl value (by simpa only [hi, bind, Option.bind] using he)
    | succ index => cases index with
      | zero => exact hr value (by simpa only [hi, bind, Option.bind] using he)
      | succ _ => simp [hi] at he

end SubtreeProofs.Rust.LookupSource.Control
