module

public import SubtreeProofs.Rust.SourceEvalAddressedReturn
public import SubtreeProofs.Rust.SourceEvalLegacyControl
public import SubtreeProofs.Rust.SourceControlSpecification

/-! Addressed execution reuses the existing source-control router and early
return executor. Actions, discriminants and return packets are concrete. Every
successful run preserves source results/costs and represented frame validity;
ordinary/intrinsic calls and whole-function storage/region closure remain open. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def instruction (callers : List Activation) (machine : World × Activation) (act : Action) :
    Option ((World × Activation) × Cost) := do
  let result ← action machine.1 machine.2 callers act
  some (result, actionCost machine.2 act)

def inspectScrutinee (callers : List Activation) (machine : World × Activation) (scrut : Scrutinee) :
    Option (Key × (World × Activation)) := do
  let (key, active) ← scrutinee machine.1 machine.2 callers scrut
  some (key, (machine.1, active))

def exec (callers : List Activation) (code : Code) (world : World) (active : Activation) : Option (Flow × Cost) :=
  Control.execWith (instruction callers) (inspectScrutinee callers)
    (fun machine => returnValue callers machine.1 machine.2) (fun machine => .next machine.1 machine.2)
    nextState {} Cost.plus (fun scrut => Cost.local (1 + scrut.weight)) code (world, active)

theorem exec_done (callers : List Activation) (world : World) (active : Activation) :
    exec callers .done world active = some (.next world active, {}) := rfl

theorem exec_ret (callers : List Activation) (world : World) (active : Activation) :
    exec callers .ret world active = returnValue callers world active := rfl

theorem exec_step (callers : List Activation) (act : Action) (rest : Code) (world : World) (active : Activation) :
    exec callers (.step act rest) world active = (do
      let (middle, current) ← action world active callers act
      let (result, last) ← exec callers rest middle current
      some (result, (actionCost active act).plus last)) := by
  simp only [exec, Control.execWith, instruction]
  cases hs : action world active callers act with
  | none => rfl
  | some result => rcases result with ⟨middle, current⟩; rfl

theorem exec_switch (callers : List Activation) (scrut : Scrutinee) (cases : List (Key × Nat))
    (fallback : Option Nat) (left right rest : Code) (world : World) (active : Activation) :
    exec callers (.switch scrut cases fallback left right rest) world active = (do
      let (key, current) ← scrutinee world active callers scrut
      let (result, first) ← Control.selectSource key cases fallback
        (fun _ => exec callers left world current) (fun _ => exec callers right world current)
      let charged := (Cost.local (1 + scrut.weight)).plus first
      match result with
      | .returned final after packet => some (.returned final after packet, charged)
      | .next middle current =>
        let (result, last) ← exec callers rest middle current
        some (result, charged.plus last)) := by
  simp only [exec, Control.execWith, inspectScrutinee]
  cases hs : scrutinee world active callers scrut with
  | none => rfl
  | some result =>
    rcases result with ⟨key, current⟩
    simp only [Bind.bind, Option.bind]
    cases hb : Control.selectSource key cases fallback _ _ with
    | none => rfl
    | some pair => rcases pair with ⟨result, cost⟩; cases result <;> rfl

theorem selectSource_simulation {α β : Type} (map : α → β) (key : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    {left right : Option α} {left' right' : Option β}
    (hl : ∀ value, left = some value → left' = some (map value))
    (hr : ∀ value, right = some value → right' = some (map value)) {value : α}
    (h : Control.selectSource key cases fallback (fun _ => left) (fun _ => right) = some value) :
    Control.selectSource key cases fallback (fun _ => left') (fun _ => right') = some (map value) := by
  simp only [Control.selectSource] at h ⊢
  cases hi : Control.selectIndex key cases fallback with
  | none => simp [hi] at h
  | some index =>
    cases index with
    | zero => exact hl value (by simpa only [hi, Bind.bind, Option.bind] using h)
    | succ index => cases index with
      | zero => exact hr value (by simpa only [hi, Bind.bind, Option.bind] using h)
      | succ _ => simp [hi] at h

theorem exec_spec (call : Calls) {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (code : Code) {result : Flow} {cost : Cost} (h : exec callers code world active = some (result, cost)) :
    SourceEval.exec call code active.state = some (result.snapshot, cost) ∧
      result.activation.frame = active.frame ∧ result.activation.count = active.count ∧ result.Valid callers := by
  induction code generalizing world active result cost with
  | done =>
    simp only [exec_done, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, ha, hw, hc, trivial⟩
  | ret =>
    obtain ⟨hs, _, hf, hn, hv, _⟩ := returnValue_spec ha hc hw h
    exact ⟨hs, hf, hn, hv⟩
  | step act rest ih =>
    rw [exec_step] at h
    cases hs : action world active callers act with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨middle, current⟩
      cases hr : exec callers rest middle current with
      | none => simp [hs, hr] at h
      | some pair =>
        rcases pair with ⟨flow, last⟩
        simp only [hs, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have step := action_spec ha hc hw act hs
        obtain ⟨hsource, hframe, hcount, hvalid⟩ := ih step.valid step.callers step.wellFormed hr
        exact ⟨by simp only [SourceEval.exec_step, step.source call, hsource, Bind.bind, Option.bind],
          hframe.trans step.frame, hcount.trans step.count, hvalid⟩
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    rw [exec_switch] at h
    cases hs : scrutinee world active callers scrut with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨key, current⟩
      obtain ⟨hsource, hframe, hcount, _, hcurrent⟩ := scrutinee_spec ha scrut hs
      cases hb : Control.selectSource key cases fallback
        (fun _ => exec callers left world current) (fun _ => exec callers right world current) with
      | none => simp [hs, hb] at h
      | some pair =>
        rcases pair with ⟨branch, first⟩
        have hbranchSource := selectSource_simulation (fun (r : Flow × Cost) => (r.1.snapshot, r.2)) key cases fallback
          (fun _ hr => (ihLeft hcurrent hc hw hr).1) (fun _ hr => (ihRight hcurrent hc hw hr).1) hb
        have hbranchValid : branch.activation.frame = current.frame ∧ branch.activation.count = current.count ∧ branch.Valid callers :=
          Control.selectSource_spec key cases fallback
            (fun _ hr => (ihLeft hcurrent hc hw hr).2) (fun _ hr => (ihRight hcurrent hc hw hr).2) hb
        simp only [hs, hb, Bind.bind, Option.bind] at h
        have hswitch := Legacy.exec_switch call scrut cases fallback left right rest active.state
        rw [hsource] at hswitch
        simp only [Bind.bind, Option.bind] at hswitch
        rw [hbranchSource] at hswitch
        cases branch with
        | returned final after packet =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨hswitch, hbranchValid.1.trans hframe, hbranchValid.2.1.trans hcount, hbranchValid.2.2⟩
        | next middle resume =>
          cases hr : exec callers rest middle resume with
          | none => simp [hr] at h
          | some pair =>
            rcases pair with ⟨flow, last⟩
            simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hrest, hf, hn, hv⟩ := ihRest hbranchValid.2.2.active hbranchValid.2.2.callers hbranchValid.2.2.wellFormed hr
            simp only [Flow.activation] at hrest
            exact ⟨by simpa only [Flow.snapshot, hrest, Bind.bind, Option.bind] using hswitch,
              hf.trans (hbranchValid.1.trans hframe), hn.trans (hbranchValid.2.1.trans hcount), hv⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
