module

public import SubtreeProofs.Rust.SourceOwnerStorage
public import SubtreeProofs.Rust.SourceEvalDerivedActions

/-! Complete owner ledgers compose through actual successful non-call action
sequences. The removed occurrence list has exactly the original source Box
destruction count; no owner is silently lost at a store or storage marker. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem action_owner_resources {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instruction : Action) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : action world active callers instruction = some (final, after)) :
    ∃ discarded,
      (active.owners world ++ (callerOwners world callers ++ external)).Perm
        (discarded ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
      discarded.length = (actionCost active instruction).destroyed.boxes ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  cases instruction with
  | storageLive slot =>
    obtain ⟨owners, callers, frame, coverage⟩ := storageLive_owner_resources ha hc hw hf covered h
    exact ⟨[], by rw [owners, callers]; simp, rfl, frame, coverage⟩
  | storageDead slot =>
    obtain ⟨owners, callers, frame, coverage⟩ := storageDead_owner_resources ha hc hw hf covered h
    exact ⟨[], by rw [owners, callers]; simp, rfl, frame, coverage⟩
  | drop slot =>
    obtain ⟨discarded, _, hl, hp, frame, coverage⟩ := drop_owner_resources ha hc hw hf covered h
    obtain ⟨_, _, _, _, hcaller⟩ := drop_owner_partition ha hc hw h
    refine ⟨discarded, ?_, hl, frame, coverage⟩
    rw [hcaller]
    simpa only [List.append_assoc] using hp.append_right (callerOwners world callers ++ external)
  | assign slot rhs =>
    have frame := assign_caller_owner_frame ha hc hw hf h
    have spec := assign_spec ha hc hw (fun _ _ => none) slot rhs h
    obtain ⟨r, hs, hpost, _⟩ := spec.2.2.2.2.2.2.2
    have callers := (scanCallers_spec hc hs).owners_preserved hpost
    obtain ⟨hp, _, _⟩ := assign_owners ha h
    refine ⟨[], ?_, rfl, frame, ?_⟩
    · rw [← callers]
      exact hp.append_right _
    · rw [← callers]
      exact assign_box_coverage ha covered h
  | fakeRead place =>
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact ⟨[], by simp, rfl, hf, covered⟩
  | call _ _ _ | undefinedBehavior => cases h

theorem actions_owner_resources {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instructions : List Action) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {cost : Cost} (h : actions world active callers instructions = some (final, after, cost)) :
    ∃ discarded,
      (active.owners world ++ (callerOwners world callers ++ external)).Perm
        (discarded ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
      discarded.length = cost.destroyed.boxes ∧ discarded.Nodup ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  induction instructions generalizing world active final after cost with
  | nil =>
    simp only [actions, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact ⟨[], by simp, rfl, by simp, hf, covered⟩
  | cons instruction rest ih =>
    cases hs : action world active callers instruction with
    | none => simp [actions, hs] at h
    | some pair =>
      rcases pair with ⟨middle, current⟩
      cases hr : actions middle current callers rest with
      | none => simp [actions, hs, hr] at h
      | some pair =>
        rcases pair with ⟨last, ending, work⟩
        simp only [actions, hs, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have step := action_spec ha hc hw instruction hs
        obtain ⟨first, hp, hl, hframe, hcovered⟩ := action_owner_resources ha hc hw instruction hf covered hs
        obtain ⟨tail, ht, hc, _, hlast, hfinal⟩ := ih step.valid step.callers step.wellFormed hframe hcovered hr
        have partition := hp.trans (ht.append_left first)
        have normalized : (active.owners world ++ (callerOwners world callers ++ external)).Perm
            ((first ++ tail) ++ (ending.owners last ++ (callerOwners last callers ++ external))) := by
          simpa only [List.append_assoc] using partition
        refine ⟨first ++ tail, normalized, ?_, (normalized.nodup_iff.mp hf.unique).of_append_left, hlast, hfinal⟩
        simp only [List.length_append, hl, hc, Cost.plus, Partial.DropWork.plus]

theorem action_box_class {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instruction : Action) (h : action world active callers instruction = some (final, after))
    (address : Nat) (hclass : world.classes address = some .box) : final.classes address = some .box := by
  cases instruction with
  | storageLive slot =>
    change storageLive world active callers slot = some (final, after) at h
    unfold storageLive at h
    split at h
    next =>
      cases hr : active.scan world with
      | none => simp [hr] at h
      | some r =>
        cases hs : scanCallers world callers with
        | none => simp [hr, hs] at h
        | some suspended =>
          simp only [hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact (world.allocate_keeps hw _ _ []).classes address .box hclass
    next => cases h
  | storageDead slot =>
    obtain ⟨_, _, _, _, _, _, he, _⟩ := storageDead_spec ha hc hw h
    simpa only [he, World.retire] using hclass
  | drop slot =>
    obtain ⟨_, _, _, _, _, _, _, he, _⟩ := drop_spec ha hc hw h
    simpa only [he, World.retire] using hclass
  | assign slot rhs =>
    rw [(assign_owners ha h).2.1]
    exact hclass
  | fakeRead _ =>
    obtain ⟨rfl, rfl⟩ := Option.some.inj h
    exact hclass
  | call _ _ _ | undefinedBehavior => cases h

theorem actions_box_class {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instructions : List Action) {cost : Cost}
    (h : actions world active callers instructions = some (final, after, cost))
    (address : Nat) (hclass : world.classes address = some .box) : final.classes address = some .box := by
  induction instructions generalizing world active final after cost with
  | nil => cases h; exact hclass
  | cons instruction rest ih =>
    cases hs : action world active callers instruction with
    | none => simp [actions, hs] at h
    | some pair =>
      rcases pair with ⟨middle, current⟩
      cases hr : actions middle current callers rest with
      | none => simp [actions, hs, hr] at h
      | some pair =>
        rcases pair with ⟨last, ending, work⟩
        simp only [actions, hs, hr, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        have step := action_spec ha hc hw instruction hs
        exact ih step.valid step.callers step.wellFormed hr (action_box_class ha hc hw instruction hs address hclass)

theorem actions_owner_destruction {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (instructions : List Action) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    {cost : Cost} (h : actions world active callers instructions = some (final, after, cost)) :
    ∃ discarded,
      (active.owners world ++ (callerOwners world callers ++ external)).Perm
        (discarded ++ (after.owners final ++ (callerOwners final callers ++ external))) ∧
      discarded.length = cost.destroyed.boxes ∧ discarded.Nodup ∧
      OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      ∀ address ∈ discarded, world.classes address = some .box ∧ final.classes address = some .box ∧
        world.live address = true ∧ final.live address = false := by
  obtain ⟨discarded, hp, hl, hn, frame, coverage⟩ := actions_owner_resources ha hc hw instructions hf covered h
  refine ⟨discarded, hp, hl, hn, frame, coverage, ?_⟩
  intro a ha
  have old := hp.symm.subset (List.mem_append_left _ ha)
  have hclass := hf.classified a old
  have hfinal := actions_box_class (address := a) ‹active.Valid world› hc hw instructions h hclass
  refine ⟨hclass, hfinal, hf.alive a old, ?_⟩
  by_cases live : final.live a = true
  · have hm := coverage a hfinal live
    exact False.elim (List.disjoint_left.mp (hp.nodup_iff.mp hf.unique).disjoint ha hm)
  · exact Bool.eq_false_iff.mpr live

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
