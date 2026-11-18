module

public import SubtreeProofs.Rust.SourceEvalHelperCalls
public import SubtreeProofs.Rust.SourceEvalAddressedControl
public import SubtreeProofs.Rust.SourceActivationLoanViews

/-! Calls join the shared addressed control engine. The callee receives the
actual post-argument activation followed by the actual suspended callers.
Readiness describes inputs on the selected concrete path, independently of
source results. Whole-program readiness and physical success remain obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage Derived

def instruction (callee : Derived.Callees) (callers : List Activation) (machine : World × Activation) :
    Action → Option ((World × Activation) × Cost)
  | .call function args slot => do
    let (world, active, cost) ← Derived.call callee machine.1 machine.2 callers function args slot
    some ((world, active), cost)
  | act => Derived.instruction callers machine act

def schedule : Code → Control.Tree (Action × Code)
  | .done => .done
  | .ret => .ret
  | .step act rest => .step (act, .step act rest) (schedule rest)
  | .switch scrut cases fallback left right rest =>
      .switch scrut cases fallback (schedule left) (schedule right) (schedule rest)

def loanInstruction (callee : Derived.Callees) (callers : List Activation) (machine : World × Activation)
    (scheduled : Action × Code) : Option ((World × Activation) × Cost) :=
  instruction callee callers (machine.1, machine.2.forgetRefs scheduled.2) scheduled.1

def exec (callee : Derived.Callees) (callers : List Activation) (code : Code) (world : World) (active : Activation) : Option (Flow × Cost) :=
  Control.execWith (loanInstruction callee callers) (inspectScrutinee callers)
    (fun machine => Derived.returnValue callers machine.1 machine.2) (fun machine => .next machine.1 machine.2)
    Derived.nextState {} Cost.plus (fun scrut => Cost.local (1 + scrut.weight)) (schedule code) (world, active)

def ReadyAt (ready : Ready) (world : World) (active : Activation) (callers : List Activation) : Action → Prop
  | .call function args _ => ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      ready world function packets
  | _ => True

/-- Only the selected arm requires readiness; unsupported routing imposes no
premise and still fails in the existing executor. -/
def SelectedReady (key : Key) (branches : List (Key × Nat)) (fallback : Option Nat) (left right : Prop) : Prop :=
  ∀ index, Control.selectIndex key branches fallback = some index → (index = 0 → left) ∧ (index = 1 → right)

def ReadyFor (callee : Derived.Callees) (ready : Ready) (callers : List Activation) : Code → World → Activation → Prop
  | .done, _, _ | .ret, _, _ => True
  | .step act rest, world, active =>
      let observed := active.forgetRefs (.step act rest)
      ReadyAt ready world observed callers act ∧
      ∀ middle current first, instruction callee callers (world, observed) act = some ((middle, current), first) →
        ReadyFor callee ready callers rest middle current
  | .switch scrut branches fallback left right rest, world, active =>
      ∀ key current, Derived.scrutinee world active callers scrut = some (key, current) →
        SelectedReady key branches fallback (ReadyFor callee ready callers left world current)
          (ReadyFor callee ready callers right world current) ∧
        ∀ middle resume first, Control.selectSource key branches fallback
            (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current) =
              some (.next middle resume, first) → ReadyFor callee ready callers rest middle resume

def noCalls : Code → Bool
  | .done | .ret => true
  | .step (.call _ _ _) _ => false
  | .step _ rest => noCalls rest
  | .switch _ _ _ left right rest => noCalls left && noCalls right && noCalls rest

theorem readyFor_noCalls (callee : Derived.Callees) (ready : Ready) (callers : List Activation)
    (code : Code) (h : noCalls code = true) (world : World) (active : Activation) :
    ReadyFor callee ready callers code world active := by
  induction code generalizing world active with
  | done | ret => trivial
  | step act rest ih =>
    cases act with
    | call _ _ _ => cases h
    | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior =>
      all_goals exact ⟨trivial, fun middle current _ _ => ih h middle current⟩
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    simp only [noCalls, Bool.and_eq_true] at h
    intro key current _
    exact ⟨fun _ _ => ⟨fun _ => ihLeft h.1.1 world current, fun _ => ihRight h.1.2 world current⟩,
      fun middle resume _ _ => ihRest h.2 middle resume⟩

structure Step (source : Calls) (world : World) (active : Activation) (callers : List Activation)
    (act : Action) (final : World) (after : Activation) (cost : Cost) : Prop where
  source : SourceEval.action source active.state act = some (after.state, cost)
  frame : after.frame = active.frame
  count : after.count = active.count
  valid : after.Valid final
  wellFormed : final.WellFormed
  suspended : ∃ r, scanCallers world callers = some r ∧ Callers final callers r ∧ Preserves world final r.reads

theorem Step.callers {source : Calls} {world final : World} {active after : Activation} {callers : List Activation}
    {act : Action} {cost : Cost} (h : Step source world active callers act final after cost) :
    ∀ a ∈ callers, a.Valid final := by
  obtain ⟨_, _, hc, _⟩ := h.suspended
  intro a hm
  obtain ⟨_, hs, _, _, _⟩ := hc.get hm
  exact hs.valid

theorem noncall_spec {source : Calls} {world final : World} {active after : Activation}
    {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (act : Action) (h : Derived.instruction callers (world, active) act = some ((final, after), cost)) :
    Step source world active callers act final after cost := by
  unfold Derived.instruction at h
  cases hr : Derived.action world active callers act with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨middle, current⟩
    simp only [hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    have hs := Derived.action_spec ha hc hw act hr
    exact ⟨hs.source source, hs.frame, hs.count, hs.valid, hs.wellFormed, hs.suspended⟩

theorem instruction_spec {callee : Derived.Callees} {source : Calls} {ready : Ready}
    (hcallee : CallsRespect callee source ready)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (act : Action) (hd : ReadyAt ready world active callers act)
    (h : instruction callee callers (world, active) act = some ((final, after), cost)) :
    Step source world active callers act final after cost := by
  cases act with
  | call function args slot =>
    unfold instruction at h
    cases hr : Derived.call callee world active callers function args slot with
    | none => simp [hr] at h
    | some result =>
      rcases result with ⟨middle, current, work⟩
      simp only [hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      obtain ⟨hs, hf, hn, _, hv, _, hw, suspended⟩ := Derived.call_spec hcallee ha hc hw function args slot hd hr
      exact ⟨hs, hf, hn, hv, hw, suspended⟩
  | storageLive slot | storageDead slot | assign slot rhs | drop slot | fakeRead place | undefinedBehavior =>
    all_goals exact noncall_spec ha hc hw _ h

theorem exec_done (callee : Derived.Callees) (callers : List Activation) (world : World) (active : Activation) :
    exec callee callers .done world active = some (.next world active, {}) := rfl

theorem exec_ret (callee : Derived.Callees) (callers : List Activation) (world : World) (active : Activation) :
    exec callee callers .ret world active = Derived.returnValue callers world active := rfl

theorem exec_step (callee : Derived.Callees) (callers : List Activation) (act : Action) (rest : Code) (world : World) (active : Activation) :
    exec callee callers (.step act rest) world active = (do
      let observed := active.forgetRefs (.step act rest)
      let ((middle, current), first) ← instruction callee callers (world, observed) act
      let (result, last) ← exec callee callers rest middle current
      some (result, first.plus last)) := rfl

theorem exec_switch (callee : Derived.Callees) (callers : List Activation) (scrut : Scrutinee) (cases : List (Key × Nat))
    (fallback : Option Nat) (left right rest : Code) (world : World) (active : Activation) :
    exec callee callers (.switch scrut cases fallback left right rest) world active = (do
      let (key, current) ← Derived.scrutinee world active callers scrut
      let (result, first) ← Control.selectSource key cases fallback
        (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current)
      let charged := (Cost.local (1 + scrut.weight)).plus first
      match result with
      | .returned final after packet => some (.returned final after packet, charged)
      | .next middle current =>
        let (result, last) ← exec callee callers rest middle current
        some (result, charged.plus last)) := by
  simp only [exec, schedule, Control.execWith, inspectScrutinee]
  cases hs : Derived.scrutinee world active callers scrut with
  | none => rfl
  | some result =>
    rcases result with ⟨key, current⟩
    simp only [Bind.bind, Option.bind]
    cases hb : Control.selectSource key cases fallback _ _ with
    | none => rfl
    | some pair => rcases pair with ⟨result, cost⟩; cases result <;> rfl

theorem selected_spec {α : Type} (key : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    {left right : Option α} {PL PR : Prop} {P : α → Prop} (hd : SelectedReady key cases fallback PL PR)
    (hl : PL → ∀ value, left = some value → P value) (hr : PR → ∀ value, right = some value → P value)
    {value : α} (h : Control.selectSource key cases fallback (fun _ => left) (fun _ => right) = some value) :
    P value := by
  simp only [Control.selectSource] at h
  cases hi : Control.selectIndex key cases fallback with
  | none => simp [hi] at h
  | some index =>
    cases index with
    | zero => exact hl ((hd 0 hi).1 rfl) value (by simpa only [hi, Bind.bind, Option.bind] using h)
    | succ index => cases index with
      | zero => exact hr ((hd 1 hi).2 rfl) value (by simpa only [hi, Bind.bind, Option.bind] using h)
      | succ _ => simp [hi] at h

theorem selected_simulation {α β : Type} (map : α → β) (key : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    {left right : Option α} {left' right' : Option β} {PL PR : Prop} (hd : SelectedReady key cases fallback PL PR)
    (hl : PL → ∀ value, left = some value → left' = some (map value))
    (hr : PR → ∀ value, right = some value → right' = some (map value)) {value : α}
    (h : Control.selectSource key cases fallback (fun _ => left) (fun _ => right) = some value) :
    Control.selectSource key cases fallback (fun _ => left') (fun _ => right') = some (map value) := by
  simp only [Control.selectSource] at h ⊢
  cases hi : Control.selectIndex key cases fallback with
  | none => simp [hi] at h
  | some index =>
    cases index with
    | zero => exact hl ((hd 0 hi).1 rfl) value (by simpa only [hi, Bind.bind, Option.bind] using h)
    | succ index => cases index with
      | zero => exact hr ((hd 1 hi).2 rfl) value (by simpa only [hi, Bind.bind, Option.bind] using h)
      | succ _ => simp [hi] at h

theorem exec_spec {callee : Derived.Callees} {call : Calls} {ready : Ready}
    (hcallee : CallsRespect callee call ready) {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (code : Code) (hd : ReadyFor callee ready callers code world active) {result : Flow} {cost : Cost} (h : exec callee callers code world active = some (result, cost)) :
    SourceEval.exec call code active.state = some (result.snapshot, cost) ∧
      result.activation.frame = active.frame ∧ result.activation.count = active.count ∧ result.Valid callers := by
  induction code generalizing world active result cost with
  | done =>
    simp only [exec_done, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, rfl, rfl, ha, hw, hc, trivial⟩
  | ret =>
    obtain ⟨hs, _, hf, hn, hv, _⟩ := Derived.returnValue_spec ha hc hw h
    exact ⟨hs, hf, hn, hv⟩
  | step act rest ih =>
    rw [exec_step] at h
    cases hs : instruction callee callers (world, active.forgetRefs (.step act rest)) act with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨⟨middle, current⟩, first⟩
      cases hr : exec callee callers rest middle current with
      | none => simp [hs, hr] at h
      | some pair =>
        rcases pair with ⟨flow, last⟩
        simp only [hs, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have step := instruction_spec hcallee (Activation.forgetRefs_valid ha (.step act rest)) hc hw act hd.1 hs
        obtain ⟨hsource, hframe, hcount, hvalid⟩ := ih step.valid step.callers step.wellFormed (hd.2 middle current first hs) hr
        refine ⟨?_, hframe.trans step.frame, hcount.trans step.count, hvalid⟩
        rw [← active.forgetRefs_source (.step act rest) call]
        simp only [SourceEval.exec_step, step.source, hsource, Bind.bind, Option.bind]
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    rw [exec_switch] at h
    cases hs : Derived.scrutinee world active callers scrut with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨key, current⟩
      obtain ⟨hsource, hframe, hcount, _, hcurrent⟩ := Derived.scrutinee_spec ha scrut hs
      obtain ⟨hselected, hresume⟩ := hd key current hs
      cases hb : Control.selectSource key cases fallback
        (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current) with
      | none => simp [hs, hb] at h
      | some pair =>
        rcases pair with ⟨branch, first⟩
        have hbranchSource := selected_simulation (fun (r : Flow × Cost) => (r.1.snapshot, r.2)) key cases fallback hselected
          (fun dom _ hr => (ihLeft hcurrent hc hw dom hr).1) (fun dom _ hr => (ihRight hcurrent hc hw dom hr).1) hb
        have hbranchValid : branch.activation.frame = current.frame ∧ branch.activation.count = current.count ∧ branch.Valid callers :=
          selected_spec key cases fallback hselected
            (fun dom _ hr => (ihLeft hcurrent hc hw dom hr).2) (fun dom _ hr => (ihRight hcurrent hc hw dom hr).2) hb
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
          cases hr : exec callee callers rest middle resume with
          | none => simp [hr] at h
          | some pair =>
            rcases pair with ⟨flow, last⟩
            simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨hrest, hf, hn, hv⟩ := ihRest hbranchValid.2.2.active hbranchValid.2.2.callers hbranchValid.2.2.wellFormed (hresume middle resume first hb) hr
            simp only [Flow.activation] at hrest
            exact ⟨by simpa only [Flow.snapshot, hrest, Bind.bind, Option.bind] using hswitch,
              hf.trans (hbranchValid.1.trans hframe), hn.trans (hbranchValid.2.1.trans hcount), hv⟩


end SubtreeProofs.Rust.SourceEval.Addressed.Calling
