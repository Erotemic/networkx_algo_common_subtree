module

public import SubtreeProofs.Rust.SourceEvalAddressedScrutinees

/-! Physical return extraction moves local zero using computed active/caller
guards and retains the resulting packet's concrete read graph. Callee storage
closure, exclusive output transfer and region escape checking remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource LookupSource.Partial LookupSource.Partial.Addressed Storage

inductive Flow where
  | next (world : World) (active : Activation)
  | returned (world : World) (active : Activation) (packet : ValueCell)

def Flow.world : Flow → World
  | .next world _ | .returned world _ _ => world

def Flow.activation : Flow → Activation
  | .next _ active | .returned _ active _ => active

def Flow.snapshot : Flow → SourceEval.Outcome
  | .next _ active => .next active.state
  | .returned _ _ packet => .returned packet.2

def Flow.readable : Flow → Prop
  | .next _ _ => True
  | .returned world _ packet => Readable world.memory world.live packet.1 packet.2

structure Flow.Valid (callers : List Activation) (result : Flow) : Prop where
  active : result.activation.Valid result.world
  wellFormed : result.world.WellFormed
  callers : ∀ a ∈ callers, a.Valid result.world
  packet : result.readable

def nextState : Flow → Option (World × Activation)
  | .next world active => some (world, active)
  | .returned _ _ _ => none

def returnValue (callers : List Activation) (world : World) (active : Activation) : Option (Flow × Cost) := do
  let current ← active.scan world
  let suspended ← scanCallers world callers
  let (packet, masks) ← Addressed.operand world active.roots (current.loans ++ suspended.reads) active.state (.move (.local 0))
  some (.returned world { active with state := masks } packet, Cost.local 1)

theorem returnValue_spec {world : World} {active : Activation} {callers : List Activation} {result : Flow} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (h : returnValue callers world active = some (result, cost)) :
    SourceEval.returnValue active.state = some (result.snapshot, cost) ∧
      result.world = world ∧ result.activation.frame = active.frame ∧ result.activation.count = active.count ∧
      result.Valid callers ∧ result.activation.state 0 = .empty := by
  unfold returnValue at h
  cases hr : active.scan world with
  | none => simp [hr] at h
  | some current =>
    cases hs : scanCallers world callers with
    | none => simp [hr, hs] at h
    | some suspended =>
      cases he : Addressed.operand world active.roots (current.loans ++ suspended.reads) active.state (.move (.local 0)) with
      | none => simp [hr, hs, he] at h
      | some found =>
        rcases found with ⟨⟨cell, value⟩, masks⟩
        simp only [hr, hs, he, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        have currentFrame := (Activation.scan_spec ha hr).frame
        obtain ⟨used, hsource, hgraph, hsub, hframe⟩ := operand_spec currentFrame he
        have hmove : active.state.move (.local 0) = some (value, masks) := by
          simpa only [SourceEval.operand] using hsource
        obtain ⟨hread, remaining, hmask, hhole, _⟩ := Partial.Locals.move_spec hmove
        have hm : (active.state 0).materialize = some value := by
          simpa only [Partial.Locals.read, splitPlace, Slot.read, Slot.get, Bind.bind, Option.bind] using hread
        have hreadable : Readable world.memory world.live cell value :=
          ⟨used, hgraph, fun a hm => currentFrame.alive a (hsub hm)⟩
        refine ⟨by simp only [SourceEval.returnValue, hm, Flow.snapshot, Bind.bind, Option.bind], rfl, rfl, rfl,
          ⟨⟨ha.1, _, hframe⟩, hw, hc, hreadable⟩, ?_⟩
        simp only [splitPlace, Slot.get, Option.some.injEq] at hhole
        subst remaining
        simp only [Flow.activation, hmask, splitPlace, Partial.Locals.set, ite_true]

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
