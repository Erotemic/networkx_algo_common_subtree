module

public import SubtreeProofs.Rust.SourceCallerResources
public import SubtreeProofs.Rust.SourceEvalCallingEntry

/-! Guarded instruction transitions preserve the complete stored caller reads
through selected branches, continuations, early returns, parsed entry and stack
cleanup. Representation alone is not used as a stored-byte preservation proof. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

theorem Callers.scan_reads {world : World} {stack : List Activation} {r : Resources}
    (h : Callers world stack r) : ∃ actual, scanCallers world stack = some actual ∧ actual.reads = r.reads := by
  have hc : ∀ a ∈ stack, a.Valid world := by
    intro a hm
    obtain ⟨_, hv, _, _, _⟩ := h.get hm
    exact hv.valid
  obtain ⟨actual, hs, hv⟩ := scanCallers_complete stack hc
  exact ⟨actual, hs, hv.reads_unique h⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem Step.preserves {world final : World} {active after : Activation} {callers : List Activation}
    {act : Action} {cost : Cost} (h : Step world active callers act final after cost) {r : Resources}
    (hs : scanCallers world callers = some r) : Preserves world final r.reads := by
  obtain ⟨actual, he, _, hp⟩ := h.suspended
  have hh := Option.some.inj (he.symm.trans hs)
  subst actual
  exact hp

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem Step.preserves {source : Calls} {world final : World} {active after : Activation} {callers : List Activation}
    {act : Action} {cost : Cost} (h : Step source world active callers act final after cost) {r : Resources}
    (hs : scanCallers world callers = some r) : Preserves world final r.reads := by
  obtain ⟨actual, he, _, hp⟩ := h.suspended
  have hh := Option.some.inj (he.symm.trans hs)
  subst actual
  exact hp

theorem exec_preserves {callee : Derived.Callees} {source : Calls} {ready : Derived.Ready}
    (hcallee : Derived.CallsRespect callee source ready) {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (code : Code) (hd : ReadyFor callee ready callers code world active) {result : Derived.Flow} {cost : Cost}
    (h : exec callee callers code world active = some (result, cost)) {r : Resources}
    (hs : scanCallers world callers = some r) : Preserves world result.world r.reads := by
  induction code generalizing world active result cost r with
  | done =>
    simp only [exec_done, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact Preserves.refl _ _
  | ret =>
    have he := (Derived.returnValue_spec ha hc hw h).2.1
    rw [he]
    exact Preserves.refl _ _
  | step act rest ih =>
    rw [exec_step] at h
    cases hi : instruction callee callers (world, active.forgetRefs (.step act rest)) act with
    | none => simp [hi] at h
    | some pair =>
      rcases pair with ⟨⟨middle, current⟩, first⟩
      cases hr : exec callee callers rest middle current with
      | none => simp [hi, hr] at h
      | some pair =>
        rcases pair with ⟨flow, last⟩
        simp only [hi, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have step := instruction_spec hcallee (Activation.forgetRefs_valid ha (.step act rest)) hc hw act hd.1 hi
        have kept := step.preserves hs
        obtain ⟨actual, hm, he⟩ := ((scanCallers_spec hc hs).transport kept).scan_reads
        have restKept := ih step.valid step.callers step.wellFormed (hd.2 middle current first hi) hr hm
        rw [he] at restKept
        exact kept.trans restKept
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
        have hbranch : Preserves world branch.world r.reads ∧ branch.Valid callers :=
          selected_spec key cases fallback
            (P := fun (pair : Derived.Flow × Cost) => Preserves world pair.1.world r.reads ∧ pair.1.Valid callers) hselected
            (fun dom pair hr => ⟨ihLeft hcurrent hc hw dom hr hs, (exec_spec hcallee hcurrent hc hw left dom hr).2.2.2⟩)
            (fun dom pair hr => ⟨ihRight hcurrent hc hw dom hr hs, (exec_spec hcallee hcurrent hc hw right dom hr).2.2.2⟩) hb
        simp only [hi, hb, Bind.bind, Option.bind] at h
        cases branch with
        | returned ending after packet =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hbranch.1
        | next middle resume =>
          cases hr : exec callee callers rest middle resume with
          | none => simp [hr] at h
          | some pair =>
            rcases pair with ⟨flow, last⟩
            simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨actual, hm, he⟩ := ((scanCallers_spec hc hs).transport hbranch.1).scan_reads
            have restKept := ihRest hbranch.2.active hbranch.2.callers hbranch.2.wellFormed
              (hresume middle resume first hb) hr hm
            rw [he] at restKept
            exact hbranch.1.trans restKept

theorem invoke_preserves {callee : Derived.Callees} {source : Calls} {ready : Derived.Ready}
    (hcallee : Derived.CallsRespect callee source ready)
    (decl : TypeReader.Definition) {world final : World} {callers : List Activation} {guards : List Nat}
    {packets : List ValueCell} {packet : ValueCell} {cost : Cost}
    (hw : world.WellFormed) (hc : ∀ a ∈ callers, a.Valid world)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (hd : ReadyFor callee ready callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
      (initialActivation world world.memory.length decl.source.localCount packets))
    (h : invoke callee callers guards decl world packets = some (final, packet, cost)) {r : Resources}
    (hs : scanCallers world callers = some r) : Preserves world final r.reads := by
  unfold invoke at h
  split at h
  next arity =>
    obtain ⟨henter, ha, hentered, hkept⟩ := enter_definition hw world.memory.length decl hp arity
    have entryKept := (hkept r.reads).preserves
    have entryCallers := (scanCallers_spec hc hs).transport entryKept
    obtain ⟨enteredReads, heScan, heReads⟩ := entryCallers.scan_reads
    have hcallers : ∀ a ∈ callers, a.Valid (world.stackCells world.memory.length (packets.map Prod.fst)) := by
      intro a hm
      obtain ⟨_, hv, _, _, _⟩ := entryCallers.get hm
      exact hv.valid
    simp only [henter, Bind.bind, Option.bind] at h
    cases hr : exec callee callers decl.source.code (world.stackCells world.memory.length (packets.map Prod.fst))
        (initialActivation world world.memory.length decl.source.localCount packets) with
    | none => simp [hr] at h
    | some pair =>
      rcases pair with ⟨flow, work⟩
      have bodyKept := exec_preserves hcallee ha hcallers hentered _ hd hr heScan
      rw [heReads] at bodyKept
      have fullKept := entryKept.trans bodyKept
      have hv := (exec_spec hcallee ha hcallers hentered _ hd hr).2.2.2
      cases flow with
      | next middle after => simp [hr] at h
      | returned middle after returned =>
        simp only [hr] at h
        cases hclose : close middle after callers guards returned with
        | none => simp [hclose] at h
        | some ending =>
          simp only [hclose, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨_, _, _, _, _, _, _, _, _, actual, hactual, _, closeKept⟩ :=
            close_spec hv.active hv.callers hv.wellFormed hv.packet hclose
          have he := (scanCallers_spec hv.callers hactual).reads_unique ((scanCallers_spec hc hs).transport fullKept)
          rw [he] at closeKept
          exact fullKept.trans closeKept
  next => cases h

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
