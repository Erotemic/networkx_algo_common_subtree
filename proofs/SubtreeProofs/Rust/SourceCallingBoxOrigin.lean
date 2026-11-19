module

public import SubtreeProofs.Rust.SourceActionBoxOrigin
public import SubtreeProofs.Rust.SourceEvalGuardedEntry

/-! Backward live-Box provenance composes through selected parsed control,
real callee dispatch, argument storage and checked return cleanup. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage

theorem instruction_boxOrigin {callee : Derived.Callees} (origin : Derived.CallsBoxOrigin callee)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (act : Action) (hd : ReadyAt Derived.TypedReady world active callers act)
    (h : instruction callee callers (world, active) act = some ((final, after), cost)) :
    BoxOrigin world final := by
  cases act with
  | call function args slot =>
    simp only [instruction, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨middle, current, work⟩, called, last⟩ := h
    cases last
    exact Derived.call_boxOrigin origin ha hc hw function args slot hd called
  | storageLive slot | storageDead slot | assign slot rhs | drop slot | fakeRead place | undefinedBehavior =>
    all_goals
      change Derived.instruction callers (world, active) _ = some ((final, after), cost) at h
      simp only [Derived.instruction, bind, Option.bind_eq_some_iff] at h
      obtain ⟨⟨middle, current⟩, acted, last⟩ := h
      cases last
      exact Derived.action_boxOrigin ha hc hw _ acted

theorem exec_boxOrigin {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady)
    (origin : Derived.CallsBoxOrigin callee)
    {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (code : Code) (hd : ReadyFor callee Derived.TypedReady callers code world active)
    {result : Derived.Flow} {cost : Cost}
    (h : exec callee callers code world active = some (result, cost)) : BoxOrigin world result.world := by
  induction code generalizing world active result cost with
  | done => cases h; exact .refl _
  | ret =>
    rw [(Derived.returnValue_spec ha hc hw h).2.1]
    exact .refl _
  | step act rest ih =>
    simp only [exec_step, bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨⟨middle, current⟩, first⟩, acted, ⟨flow, last⟩, resumed, ending⟩ := h
    cases ending
    have valid := Activation.forgetRefs_valid ha (.step act rest)
    have step := instruction_spec respects valid hc hw act hd.1 acted
    exact (instruction_boxOrigin origin valid hc hw act hd.1 acted).trans
      (ih step.valid step.callers step.wellFormed (hd.2 middle current first acted) resumed)
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    rw [exec_switch] at h
    cases hi : Derived.scrutinee world active callers scrut with
    | none => simp [hi] at h
    | some pair =>
      rcases pair with ⟨key, current⟩
      have hcurrent := (Derived.scrutinee_spec ha scrut hi).2.2.2.2
      obtain ⟨hselected, hresume⟩ := hd key current hi
      cases hb : Control.selectSource key cases fallback
          (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current) with
      | none => simp [hi, hb] at h
      | some pair =>
        rcases pair with ⟨branch, first⟩
        have hbranch : BoxOrigin world branch.world ∧ branch.Valid callers :=
          selected_spec key cases fallback
            (P := fun (pair : Derived.Flow × Cost) => BoxOrigin world pair.1.world ∧ pair.1.Valid callers) hselected
            (fun dom pair hr => ⟨ihLeft hcurrent hc hw dom hr, (exec_spec respects hcurrent hc hw left dom hr).2.2.2⟩)
            (fun dom pair hr => ⟨ihRight hcurrent hc hw dom hr, (exec_spec respects hcurrent hc hw right dom hr).2.2.2⟩) hb
        simp only [hi, hb, bind, Option.bind] at h
        cases branch with
        | returned ending after packet => cases h; exact hbranch.1
        | next middle resume =>
          cases resumed : exec callee callers rest middle resume with
          | none => simp [resumed] at h
          | some pair =>
            rcases pair with ⟨flow, last⟩
            simp only [resumed, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hbranch.1.trans (ihRest hbranch.2.active hbranch.2.callers hbranch.2.wellFormed
              (hresume middle resume first hb) resumed)

theorem invoke_boxOrigin {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady)
    (origin : Derived.CallsBoxOrigin callee)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee Derived.TypedReady callers decl.source.code
      (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : invoke callee callers guards decl world packets = some (final, packet, cost)) :
    BoxOrigin world final := by
  unfold invoke at h
  split at h
  next arity =>
    obtain ⟨henter, ha, hentered, hkept⟩ := enter_definition hw world.memory.length decl hp arity
    simp only [henter, bind, Option.bind] at h
    cases body : exec callee callers decl.source.code
        (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets) with
    | none => simp [body] at h
    | some pair =>
      rcases pair with ⟨flow, work⟩
      simp only [body] at h
      have ending := h
      have hcallers : ∀ a ∈ callers, a.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
        intro a hm
        obtain ⟨bound, used, hf⟩ := hc a hm
        exact ⟨bound, used, hf.preserve (hkept used).preserves⟩
      have bodyOrigin := exec_boxOrigin respects origin ha hcallers hentered _ hd body
      have checked := (exec_spec respects ha hcallers hentered _ hd body).2.2.2
      cases flow with
      | next middle after => cases ending
      | returned middle after returned =>
        cases closed : close middle after callers guards returned with
        | none => simp [closed] at ending
        | some endingWorld =>
          simp only [closed, Option.some.injEq, Prod.mk.injEq] at ending
          obtain ⟨rfl, rfl, rfl⟩ := ending
          rw [(close_spec checked.active checked.callers checked.wellFormed checked.packet closed).1]
          exact ((world.stackCells_boxOrigin _ _).trans bodyOrigin).trans (middle.retire_boxOrigin _)
  next => cases h

theorem guardedInvoke_boxOrigin {callee : Derived.Callees} {source : Calls}
    (respects : Derived.CallsRespect callee source Derived.TypedReady)
    (origin : Derived.CallsBoxOrigin callee)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee Derived.TypedReady callers decl.source.code
      (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : guardedInvoke callee callers guards decl world packets = some (final, packet, cost)) :
    BoxOrigin world final := by
  simp only [guardedInvoke, bind, Option.bind_eq_some_iff] at h
  obtain ⟨_, _, h⟩ := h
  split at h
  · exact invoke_boxOrigin respects origin decl hw hc hp hd h
  · cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
