module

public import SubtreeProofs.Rust.SourceEvalDerivedDrop

/-! Executable non-call actions and straight-line composition over the current
addressed activation. Every successful step retains its original source cost.
Calls, switches, returns and complete program check success remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def action (world : World) (active : Activation) (callers : List Activation) : Action → Option (World × Activation)
  | .storageLive slot => storageLive world active callers slot
  | .storageDead slot => storageDead world active callers slot
  | .assign slot rhs => assign world active callers slot rhs
  | .drop slot => drop world active callers slot
  | .fakeRead _ => some (world, active)
  | .call _ _ _ | .undefinedBehavior => none

def actionCost (active : Activation) (instruction : Action) : Cost :=
  Cost.local instruction.weight (match instruction with | .drop slot => (active.state slot).dropWork | _ => {})

theorem action_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) (instruction : Action)
    (h : action world active callers instruction = some (final, after)) :
    Step world active callers instruction final after (actionCost active instruction) := by
  cases instruction with
  | storageLive slot => exact storageLive_spec ha hc hw h
  | storageDead slot => exact (storageDead_spec ha hc hw h).1
  | drop slot => exact (drop_spec ha hc hw h).1
  | assign slot rhs =>
    have hs := assign_spec ha hc hw (fun _ _ => none) slot rhs h
    exact ⟨fun call => (assign_spec ha hc hw call slot rhs h).1,
      hs.2.1, hs.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2⟩
  | fakeRead place =>
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    obtain ⟨suspended, hs, hv⟩ := scanCallers_complete callers hc
    exact ⟨fun _ => rfl, rfl, rfl, ha, hw, suspended, hs, hv, Preserves.refl _ _⟩
  | call _ _ _ | undefinedBehavior => cases h

def actions (world : World) (active : Activation) (callers : List Activation) : List Action → Option (World × Activation × Cost)
  | [] => some (world, active, {})
  | instruction :: rest => do
    let (middle, current) ← action world active callers instruction
    let (final, after, last) ← actions middle current callers rest
    some (final, after, (actionCost active instruction).plus last)

theorem actions_spec {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed) (instructions : List Action)
    (h : actions world active callers instructions = some (final, after, cost)) :
    (∀ call, SourceEval.exec call (instructions.foldr Control.Tree.step .done) active.state =
      some (.next after.state, cost)) ∧
      after.frame = active.frame ∧ after.count = active.count ∧ after.Valid final ∧
      (∀ a ∈ callers, a.Valid final) ∧ final.WellFormed := by
  induction instructions generalizing world active final after cost with
  | nil =>
    simp only [actions, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨fun _ => rfl, rfl, rfl, ha, hc, hw⟩
  | cons instruction rest ih =>
    unfold actions at h
    cases hs : action world active callers instruction with
    | none => simp [hs] at h
    | some result =>
      rcases result with ⟨middle, current⟩
      cases hr : actions middle current callers rest with
      | none => simp [hs, hr] at h
      | some result =>
        rcases result with ⟨last, ending, work⟩
        simp only [hs, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have step := action_spec ha hc hw instruction hs
        obtain ⟨hsource, hframe, hcount, hvalid, hcallers, hworld⟩ := ih step.valid step.callers step.wellFormed hr
        refine ⟨?_, hframe.trans step.frame, hcount.trans step.count, hvalid, hcallers, hworld⟩
        intro call
        simp only [List.foldr_cons, SourceEval.exec_step, step.source call, hsource call, Bind.bind, Option.bind]

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
