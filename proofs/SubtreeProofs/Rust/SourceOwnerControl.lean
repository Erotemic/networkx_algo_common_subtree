module

public import SubtreeProofs.Rust.SourceOwnerCallTransfer

/-! Complete owner resources through actual selected calling control and early
returns, including certified unused-reference views. Every temporary packet is
accounted for; source/cost and frame validity remain the existing contracts. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem scrutinee_owners {world : World} {active : Activation} (ha : active.Valid world)
    {guarded : List Nat} (scrut : Scrutinee) {key : Key} {after : State}
    (h : Addressed.scrutinee world active.roots guarded active.state scrut = some (key, after)) :
    (active.owners world).Perm (({active with state := after} : Activation).owners world) := by
  cases scrut with
  | discriminant place =>
    cases hd : discriminant world active.roots active.state place with
    | none => simp [Addressed.scrutinee, hd] at h
    | some actual =>
      simp only [Addressed.scrutinee, hd, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact .rfl
  | value op =>
    cases ho : operand world active.roots guarded active.state (Legacy.operandMap op) with
    | none => simp [Addressed.scrutinee, ho] at h
    | some pair =>
      rcases pair with ⟨⟨cell, value⟩, masks⟩
      obtain ⟨owners, footprint, partition⟩ := operand_owners ha ho
      cases cell with
      | number _ | node _ _ _ | shared _ | owned _ => simp [Addressed.scrutinee, ho] at h
      | boolean b =>
        cases footprint
        simp only [Addressed.scrutinee, ho, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact partition

namespace Derived

def Flow.OwnerResources (callers : List Activation) (external : List Nat) : Flow → Prop
  | .next world active =>
    OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)) ∧
      BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external))
  | .returned world active packet =>
    ∃ owners, Footprint world.memory packet.1 owners ∧
      OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))) ∧
      BoxCoverage world (owners ++ (active.owners world ++ (callerOwners world callers ++ external)))

theorem scrutinee_owner_resources {world : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (scrut : Scrutinee) {key : Key} {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : Derived.scrutinee world active callers scrut = some (key, after)) :
    Flow.OwnerResources callers external (.next world after) := by
  unfold Derived.scrutinee at h
  cases hr : active.scan world with
  | none => simp [hr] at h
  | some current =>
    cases hs : scanCallers world callers with
    | none => simp [hr, hs] at h
    | some suspended =>
      cases he : Addressed.scrutinee world active.roots (current.loans ++ suspended.reads) active.state scrut with
      | none => simp [hr, hs, he] at h
      | some pair =>
        rcases pair with ⟨actual, masks⟩
        simp only [hr, hs, he, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have partition := (Addressed.scrutinee_owners ha scrut he).append_right (callerOwners world callers ++ external)
        exact ⟨hf.perm partition, covered.perm partition⟩

theorem returnValue_owner_resources {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {result : Flow} {cost : Cost} (h : returnValue callers world active = some (result, cost)) :
    result.OwnerResources callers external := by
  obtain ⟨after, packet, owners, rfl, footprint, frame, hp⟩ := returnValue_owner_frame ha hf h
  refine ⟨owners, footprint, frame, ?_⟩
  exact covered.perm (by simpa only [List.append_assoc] using hp.append_right (callerOwners world callers ++ external))

end Derived
end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Calling

open LookupSource Heap Partial Partial.Addressed Storage Derived

theorem noncall_owner_resources {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (act : Action) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : Derived.instruction callers (world, active) act = some ((final, after), cost)) :
    Flow.OwnerResources callers external (.next final after) := by
  unfold Derived.instruction at h
  cases hr : Derived.action world active callers act with
  | none => simp [hr] at h
  | some pair =>
    rcases pair with ⟨middle, current⟩
    simp only [hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
    obtain ⟨_, _, _, frame, coverage⟩ := Derived.action_owner_resources ha hc hw act hf covered hr
    exact ⟨frame, coverage⟩

theorem instruction_owner_resources {callee : Derived.Callees} {source : Calls}
    (hcallee : CallsRespect callee source TypedReady) (howns : CallsOwn callee)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (act : Action) (hd : ReadyAt TypedReady world active callers act) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : instruction callee callers (world, active) act = some ((final, after), cost)) :
    Flow.OwnerResources callers external (.next final after) := by
  cases act with
  | call function args slot =>
    unfold instruction at h
    cases hr : Derived.call callee world active callers function args slot with
    | none => simp [hr] at h
    | some result =>
      rcases result with ⟨middle, current, work⟩
      simp only [hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      exact Derived.call_owner_resources hcallee howns ha hc hw function args slot hf covered hd hr
  | storageLive _ | storageDead _ | assign _ _ | drop _ | fakeRead _ | undefinedBehavior =>
    all_goals exact noncall_owner_resources ha hc hw _ hf covered h

theorem exec_owner_resources {callee : Derived.Callees} {source : Calls}
    (hcallee : CallsRespect callee source TypedReady) (howns : CallsOwn callee)
    {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (code : Code) (hd : ReadyFor callee TypedReady callers code world active) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {result : Flow} {cost : Cost} (h : exec callee callers code world active = some (result, cost)) :
    result.OwnerResources callers external := by
  induction code generalizing world active result cost with
  | done =>
    simp only [exec_done, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hf, covered⟩
  | ret => exact Derived.returnValue_owner_resources ha hf covered h
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
        have observed := Activation.forgetRefs_valid ha (.step act rest)
        have resources := instruction_owner_resources hcallee howns observed hc hw act hd.1
          (by simpa only [Activation.forgetRefs_owners] using hf)
          (by simpa only [Activation.forgetRefs_owners] using covered) hs
        have step := instruction_spec hcallee observed hc hw act hd.1 hs
        exact ih step.valid step.callers step.wellFormed (hd.2 middle current first hs) resources.1 resources.2 hr
  | switch scrut cases fallback left right rest ihLeft ihRight ihRest =>
    rw [exec_switch] at h
    cases hs : Derived.scrutinee world active callers scrut with
    | none => simp [hs] at h
    | some pair =>
      rcases pair with ⟨key, current⟩
      have currentValid := (Derived.scrutinee_spec ha scrut hs).2.2.2.2
      have resources := Derived.scrutinee_owner_resources ha scrut hf covered hs
      obtain ⟨selected, resume⟩ := hd key current hs
      cases hb : Control.selectSource key cases fallback
        (fun _ => exec callee callers left world current) (fun _ => exec callee callers right world current) with
      | none => simp [hs, hb] at h
      | some pair =>
        rcases pair with ⟨branch, first⟩
        have owned : branch.OwnerResources callers external := selected_spec key cases fallback selected
          (fun dom _ hr => ihLeft currentValid hc hw dom resources.1 resources.2 hr)
          (fun dom _ hr => ihRight currentValid hc hw dom resources.1 resources.2 hr) hb
        have valid : branch.Valid callers := selected_spec key cases fallback selected
          (fun dom _ hr => (exec_spec hcallee currentValid hc hw left dom hr).2.2.2)
          (fun dom _ hr => (exec_spec hcallee currentValid hc hw right dom hr).2.2.2) hb
        simp only [hs, hb, Bind.bind, Option.bind] at h
        cases branch with
        | returned final after packet =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact owned
        | next middle active =>
          cases hr : exec callee callers rest middle active with
          | none => simp [hr] at h
          | some pair =>
            rcases pair with ⟨flow, last⟩
            simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ihRest valid.active valid.callers valid.wellFormed (resume middle active first hb) owned.1 owned.2 hr

end SubtreeProofs.Rust.SourceEval.Addressed.Calling
