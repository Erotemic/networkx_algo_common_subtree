module

public import SubtreeProofs.Rust.LookupSourceControl

/-! Exact successful-run extension for the shared source-control executor.
Primitive handlers may become more defined; completed outcomes and costs are
preserved without imposing a particular state, outcome or work representation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Control

theorem selectSource_extends {α : Type} (actual : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    {left right left' right' : Option α}
    (hl : ∀ value, left = some value → left' = some value)
    (hr : ∀ value, right = some value → right' = some value)
    {value : α} (he : selectSource actual cases fallback (fun _ => left) (fun _ => right) = some value) :
    selectSource actual cases fallback (fun _ => left') (fun _ => right') = some value := by
  simp only [selectSource] at he ⊢
  cases hi : selectIndex actual cases fallback with
  | none => simp [hi] at he
  | some index =>
    cases index with
    | zero => exact hl value (by simpa only [hi, bind, Option.bind] using he)
    | succ index => cases index with
      | zero => exact hr value (by simpa only [hi, bind, Option.bind] using he)
      | succ _ => simp [hi] at he

theorem execWith_extends {A S R C : Type}
    (first second : S → A → Option (S × C))
    (hc : ∀ state action pair, first state action = some pair → second state action = some pair)
    (scrutinee : S → Scrutinee → Option (Key × S))
    (returnValue : S → Option (R × C)) (finish : S → R) (nextState : R → Option S)
    (zero : C) (plus : C → C → C) (branchWork : Scrutinee → C)
    (code : Tree A) {state : S} {pair : R × C}
    (hr : execWith first scrutinee returnValue finish nextState zero plus branchWork code state = some pair) :
    execWith second scrutinee returnValue finish nextState zero plus branchWork code state = some pair := by
  induction code generalizing state pair with
  | done => exact hr
  | ret => exact hr
  | step action rest ih =>
    simp only [execWith, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨middle, current⟩, ha, ⟨⟨result, last⟩, he, final⟩⟩ := hr
    exact ⟨_, hc state action _ ha, _, ih he, final⟩
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    simp only [execWith, bind, Option.bind_eq_some_iff] at hr ⊢
    obtain ⟨⟨actual, middle⟩, hs, ⟨⟨result, current⟩, ha, final⟩⟩ := hr
    have choice := selectSource_extends actual cases fallback (fun _ hp => ihLeft hp) (fun _ hp => ihRight hp) ha
    refine ⟨_, hs, _, choice, ?_⟩
    cases hn : nextState result with
    | none => simpa only [hn] using final
    | some next =>
      simp only [hn, Option.bind_eq_some_iff] at final ⊢
      obtain ⟨⟨result, last⟩, he, final⟩ := final
      exact ⟨_, ihRest he, final⟩

end SubtreeProofs.Rust.LookupSource.Control
