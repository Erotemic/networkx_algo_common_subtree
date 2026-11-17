module

public import SubtreeProofs.Rust.SourceActivationInventory

/-! Assignment derives active move guards, suspended caller resources and the
actual remaining store context. RHS evaluation occurs once. All inventories
come from bounded roots/masks; no preselected guard or post-RHS frame is an input.
Global ownership separation, control/callee traces and regions remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

def store (world : World) (roots : Roots) (frame slot : Nat) (retained : List Nat)
    (middle : State) (packet : ValueCell) : Option (World × State) := do
  if emptySlot (middle slot) then
    let binding ← roots slot
    let used ← traceGraph world.memory packet.1 packet.2
    let after ← world.writeStack frame slot binding (retained ++ used) packet.1
    some (after, middle.set slot (Slot.ofValue packet.2))
  else none

theorem assign_eq_store {world : World} {roots : Roots} {frame slot : Nat} {blocked retained : List Nat}
    {state middle : State} {packet : ValueCell} {rhs : Expr}
    (h : Addressed.expression world roots blocked state rhs = some (packet, middle)) :
    Addressed.assign world roots frame blocked retained state slot rhs = store world roots frame slot retained middle packet := by
  rcases packet with ⟨cell, value⟩
  simp only [Addressed.assign, h, store, Bind.bind, Option.bind]

def assign (world : World) (active : Activation) (callers : List Activation) (slot : Nat) (rhs : Expr) : Option (World × Activation) := do
  let current ← active.scan world
  let suspended ← scanCallers world callers
  let (packet, middle) ← Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs
  let remainder ← ({ active with state := middle } : Activation).scanExcept world slot
  let (after, state) ← store world active.roots active.frame slot (remainder.reads ++ suspended.reads) middle packet
  some (after, { active with state := state })

theorem assign_run {world after : World} {active : Activation} {callers : List Activation} {slot : Nat} {rhs : Expr}
    {current suspended remainder : Resources} {packet : ValueCell} {middle state : State}
    (ha : active.scan world = some current) (hc : scanCallers world callers = some suspended)
    (he : Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs = some (packet, middle))
    (hr : ({ active with state := middle } : Activation).scanExcept world slot = some remainder)
    (hs : store world active.roots active.frame slot (remainder.reads ++ suspended.reads) middle packet = some (after, state)) :
    assign world active callers slot rhs = some (after, { active with state := state }) := by
  simp only [assign, ha, hc, he, hr, hs, Bind.bind, Option.bind]

theorem assign_spec {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (call : Calls) (slot : Nat) (rhs : Expr)
    (h : assign world active callers slot rhs = some (final, after)) :
    SourceEval.action call active.state (.assign slot rhs) = some (after.state, Cost.local (Action.assign slot rhs).weight) ∧
      after.frame = active.frame ∧ after.count = active.count ∧ after.roots = active.roots ∧ after.Valid final ∧
      (∀ a ∈ callers, a.Valid final) ∧ final.WellFormed ∧
      ∃ suspended, scanCallers world callers = some suspended ∧ Callers final callers suspended := by
  unfold assign at h
  cases hcurrent : active.scan world with
  | none => simp [hcurrent] at h
  | some current =>
    cases hsuspended : scanCallers world callers with
    | none => simp [hcurrent, hsuspended] at h
    | some suspended =>
      cases he : Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs with
      | none => simp [hcurrent, hsuspended, he] at h
      | some result =>
        rcases result with ⟨packet, middle⟩
        cases hr : ({ active with state := middle } : Activation).scanExcept world slot with
        | none => simp [hcurrent, hsuspended, he, hr] at h
        | some remainder =>
          cases hs : store world active.roots active.frame slot (remainder.reads ++ suspended.reads) middle packet with
          | none => simp [hcurrent, hsuspended, he, hr, hs] at h
          | some result =>
            rcases result with ⟨next, state⟩
            simp only [hcurrent, hsuspended, he, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            have hactive := Activation.scan_spec ha hcurrent
            have hcallers := scanCallers_spec hc hsuspended
            obtain ⟨used, _, _, _, hmid⟩ := expression_spec hactive.frame he
            have hvalid : ({ active with state := middle } : Activation).Valid world :=
              ⟨hactive.bounded, current.reads, hmid⟩
            have hcontext := Activation.context_spec hvalid slot hr
            have hlive : AliveOn world.live (remainder.reads ++ suspended.reads) := by
              intro a ha
              rcases List.mem_append.mp ha with ha | ha
              · exact hcontext.alive a ha
              · exact hcallers.alive a ha
            have hcontext' := hcontext.weaken (fun _ ha => List.mem_append_left _ ha) hlive
            have hold : Addressed.assign world active.roots active.frame (current.loans ++ suspended.reads)
                (remainder.reads ++ suspended.reads) active.state slot rhs = some (next, state) :=
              (assign_eq_store he).trans hs
            rcases packet with ⟨cell, value⟩
            have hselector : ∀ raw snapshot masks,
                Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs =
                  some ((raw, snapshot), masks) →
                Frame world active.frame (active.roots.set slot none) (masks.set slot .empty)
                  (remainder.reads ++ suspended.reads) := by
              intro raw snapshot masks hh
              rw [he] at hh
              have hp := Option.some.inj hh
              simp only [Prod.mk.injEq] at hp
              obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
              exact hcontext'
            obtain ⟨_, _, _, _, _, _, _, hsource, _, _, hframe, _, hkeep, hworld⟩ :=
              Addressed.assign_spec hactive.frame hw call rhs hselector hold
            have hfinalCallers := hcallers.transport (hkeep.weaken (fun _ ha => List.mem_append_right _ ha))
            refine ⟨hsource, rfl, rfl, rfl, ?_, ?_, hworld, suspended, rfl, hfinalCallers⟩
            · exact ⟨hactive.bounded, _, hframe⟩
            · intro a hm
              obtain ⟨_, hv, _, _, _⟩ := hfinalCallers.get hm
              exact hv.valid

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
