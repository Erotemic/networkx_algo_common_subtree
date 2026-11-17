module

public import SubtreeProofs.Rust.SourceEvalDerivedActions
public import SubtreeProofs.Rust.SourceEvalTypeExecution

/-! Switch discriminants inspect actual retained constructor tags without
materializing moved fields. Boolean scrutinees use the existing addressed
operand executor and physical move policy. Source agreement is separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem Frame.locate_node {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals} {guards : List Nat}
    (h : Frame world frame roots state guards) (place : Place) {kind : Kind} {tag : Nat} {parts : List Slot}
    (hr : (state (splitPlace place).1).get (splitPlace place).2 = some (.node kind tag parts)) :
    ∃ cells pointer used, Storage.locate world roots place = some (.node kind tag cells, pointer) ∧
      PartialGraphFields world.memory cells parts used ∧ used ++ [pointer.root] ⊆ guards := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [hp] at hr
  cases hb : roots slot with
  | none =>
    have he : state slot = .empty := by simpa only [hb] using h.slots slot
    rw [he] at hr
    cases path with
    | nil => cases hr
    | cons step rest => cases step <;> cases hr
  | some binding =>
    obtain ⟨cell, all, hc, _, hg, hs⟩ := h.get hb
    have hread : read world.memory ⟨binding.address, []⟩ = some cell := by
      simp only [Heap.read, hc, Bind.bind, Option.bind, Heap.fields]
    obtain ⟨found, pointer, used, hl, _, hh, hu⟩ := hg.locate ⟨binding.address, []⟩ hread path hr
    cases hh with
    | node fields =>
      exact ⟨_, pointer, used, by simp only [Storage.locate, hp, hb, hc, hl, Bind.bind, Option.bind],
        fields, fun _ ha => hs (hu ha)⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def discriminant (world : World) (roots : Roots) (state : State) (place : Place) : Option Key := do
  let (slot, path) := splitPlace place
  match ← (state slot).get path with
  | .node _ _ _ =>
    let (cell, pointer) ← Storage.locate world roots place
    if world.live pointer.root then
      match cell with | .node kind tag _ => some (.variant kind tag) | _ => none
    else none
  | _ => none

theorem discriminant_complete {world : World} {frame : Nat} {roots : Roots} {state : State} {guards : List Nat}
    (hf : Frame world frame roots state guards) (place : Place) {kind : Kind} {tag : Nat} {parts : List Slot}
    (hr : (state (splitPlace place).1).get (splitPlace place).2 = some (.node kind tag parts)) :
    discriminant world roots state place = some (.variant kind tag) := by
  obtain ⟨cells, pointer, used, hl, _, hu⟩ := hf.locate_node place hr
  have ha : world.live pointer.root = true := hf.alive _ (hu (List.mem_append_right _ (by simp)))
  rcases hp : splitPlace place with ⟨slot, path⟩
  simp only [hp] at hr
  simp only [discriminant, hp, hr, hl, ha, ite_true, Bind.bind, Option.bind]

theorem discriminant_spec {world : World} {frame : Nat} {roots : Roots} {state : State} {guards : List Nat}
    (hf : Frame world frame roots state guards) {place : Place} {key : Key}
    (h : discriminant world roots state place = some key) :
    SourceEval.scrutinee state (.discriminant place) = some (key, state) := by
  rcases hp : splitPlace place with ⟨slot, path⟩
  cases hg : (state slot).get path with
  | none => simp [discriminant, hp, hg] at h
  | some part =>
    cases part with
    | empty | boolean _ | number _ | shared _ | boxed _ => simp [discriminant, hp, hg] at h
    | node kind tag parts =>
      have he := discriminant_complete hf place (by simpa only [hp] using hg)
      rw [he] at h
      cases h
      simp only [SourceEval.scrutinee, hp, hg, Bind.bind, Option.bind]

def scrutinee (world : World) (roots : Roots) (guarded : List Nat) (state : State) : Scrutinee → Option (Key × State)
  | .discriminant place => do
    let key ← discriminant world roots state place
    some (key, state)
  | .value op => do
    let ((cell, _), after) ← operand world roots guarded state (Legacy.operandMap op)
    match cell with | .boolean b => some (.boolean b, after) | _ => none

theorem scrutinee_spec {world : World} {frame : Nat} {roots : Roots} {state after : State} {guards guarded : List Nat}
    (hf : Frame world frame roots state guards) (scrut : Scrutinee) {key : Key}
    (h : scrutinee world roots guarded state scrut = some (key, after)) :
    SourceEval.scrutinee state scrut = some (key, after) ∧ Frame world frame roots after guards := by
  cases scrut with
  | discriminant place =>
    cases hd : discriminant world roots state place with
    | none => simp [scrutinee, hd] at h
    | some actual =>
      simp only [scrutinee, hd, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨discriminant_spec hf hd, hf⟩
  | value op =>
    cases ho : operand world roots guarded state (Legacy.operandMap op) with
    | none => simp [scrutinee, ho] at h
    | some result =>
      rcases result with ⟨⟨cell, value⟩, final⟩
      obtain ⟨used, hs, hg, _, hframe⟩ := operand_spec hf ho
      cases hg with
      | number _ | node _ | shared _ _ | owned _ _ => simp [scrutinee, ho] at h
      | boolean b =>
        simp only [scrutinee, ho, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ⟨by simp only [Types.scrutinee_value, hs, Bind.bind, Option.bind], hframe⟩

end SubtreeProofs.Rust.SourceEval.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def scrutinee (world : World) (active : Activation) (callers : List Activation) (scrut : Scrutinee) :
    Option (Key × Activation) := do
  let current ← active.scan world
  let suspended ← scanCallers world callers
  let (key, after) ← Addressed.scrutinee world active.roots (current.loans ++ suspended.reads) active.state scrut
  some (key, { active with state := after })

theorem scrutinee_spec {world : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (scrut : Scrutinee) {key : Key}
    (h : scrutinee world active callers scrut = some (key, after)) :
    SourceEval.scrutinee active.state scrut = some (key, after.state) ∧
      after.frame = active.frame ∧ after.count = active.count ∧ after.roots = active.roots ∧ after.Valid world := by
  unfold scrutinee at h
  cases hr : active.scan world with
  | none => simp [hr] at h
  | some current =>
    cases hs : scanCallers world callers with
    | none => simp [hr, hs] at h
    | some suspended =>
      cases he : Addressed.scrutinee world active.roots (current.loans ++ suspended.reads) active.state scrut with
      | none => simp [hr, hs, he] at h
      | some result =>
        rcases result with ⟨actual, masks⟩
        simp only [hr, hs, he, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hsource, hframe⟩ := Addressed.scrutinee_spec (Activation.scan_spec ha hr).frame scrut he
        exact ⟨hsource, rfl, rfl, rfl, ha.1, _, hframe⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
