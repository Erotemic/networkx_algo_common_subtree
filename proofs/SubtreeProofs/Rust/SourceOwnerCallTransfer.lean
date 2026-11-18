module

public import SubtreeProofs.Rust.SourceOwnerCallees

/-! Whole actual call ownership: one-pass argument extraction, the complete
callee-owned output and the existing guarded destination store compose without
supplied intermediate ledgers or a post-callee frame. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

theorem store_owner_resources {world final : World} {active : Activation} {slot : Nat} {retained : List Nat}
    {packet : ValueCell} {after : State} {callers : List Activation} {r : Resources} {owners external : List Nat}
    (hw : world.WellFormed) (bound : Bounded active.roots active.count)
    (context : Frame world active.frame (active.roots.set slot none) (active.state.set slot .empty) retained)
    (hc : Callers world callers r) (hr : r.reads ⊆ retained)
    (hp : Readable world.memory world.live packet.1 packet.2) (ho : Footprint world.memory packet.1 owners)
    (hf : OwnerFrame world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (covered : BoxCoverage world (owners ++ (active.owners world ++ (callerOwners world callers ++ external))))
    (h : store world active.roots active.frame slot retained active.state packet = some (final, after)) :
    OwnerFrame final (({active with state := after} : Activation).owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (({active with state := after} : Activation).owners final ++ (callerOwners final callers ++ external)) := by
  obtain ⟨partition, classes, live⟩ := store_owners bound context (fun _ ha => ha) hp ho h
  have stable := (store_spec hw context hp h).2.2.1
  have hcallers := hc.owners_preserved (hc.transport (stable.weaken hr))
  have perm : (owners ++ (active.owners world ++ (callerOwners world callers ++ external))).Perm
      (({active with state := after} : Activation).owners final ++ (callerOwners world callers ++ external)) := by
    simpa only [List.append_assoc] using partition.symm.append_right (callerOwners world callers ++ external)
  have frame := hf.perm perm
  have coverage := covered.perm perm
  rw [← hcallers]
  refine ⟨⟨frame.unique, ?_, ?_⟩, ?_⟩
  · intro a ha
    rw [classes]
    exact frame.classified a ha
  · intro a ha
    rw [live]
    exact frame.alive a ha
  · intro a hc hl
    rw [classes] at hc
    rw [live] at hl
    exact coverage a hc hl

theorem call_owner_resources {callee : Callees} {source : Calls}
    (hcallee : CallsRespect callee source TypedReady) (howns : CallsOwn callee)
    {world final : World} {active after : Activation} {callers : List Activation} {cost : Cost}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    (function : Function) (args : List Operand) (slot : Nat) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (covered : BoxCoverage world (active.owners world ++ (callerOwners world callers ++ external)))
    (hready : ∀ current suspended packets masks, active.scan world = some current →
      scanCallers world callers = some suspended →
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) →
      TypedReady world function packets)
    (h : call callee world active callers function args slot = some (final, after, cost)) :
    OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (after.owners final ++ (callerOwners final callers ++ external)) := by
  unfold call at h
  cases hcurrent : active.scan world with
  | none => simp [hcurrent] at h
  | some current =>
    cases hsuspended : scanCallers world callers with
    | none => simp [hcurrent, hsuspended] at h
    | some suspended =>
      cases hargs : Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args with
      | none => simp [hcurrent, hsuspended, hargs] at h
      | some pair =>
        rcases pair with ⟨packets, masks⟩
        cases hrest : ({ active with state := masks } : Activation).scanExcept world slot with
        | none => simp [hcurrent, hsuspended, hargs, hrest] at h
        | some remainder =>
          cases hb : active.roots slot with
          | none => simp [hcurrent, hsuspended, hb] at h
          | some binding =>
            simp only [hcurrent, hsuspended, hargs, hrest, hb, Bind.bind, Option.bind] at h
            cases hrun : callee world ((remainder.reads ++ suspended.reads) ++ [binding.address])
                ({ active with state := masks } :: callers) function packets with
            | none => simp only [hrun] at h; cases h
            | some returned =>
              rcases returned with ⟨returned, packet, inner⟩
              simp only [hrun] at h
              cases hstore : store returned active.roots active.frame slot (remainder.reads ++ suspended.reads) masks packet with
              | none => simp only [hstore] at h; cases h
              | some result =>
                rcases result with ⟨next, state⟩
                simp only [hstore, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl, rfl⟩ := h
                have currentFrame := (Activation.scan_spec ha hcurrent).frame
                have callerFrame := scanCallers_spec hc hsuspended
                obtain ⟨used, _, graph, subset, middleFrame⟩ := Addressed.operands_spec currentFrame args hargs
                have middleValid : ({ active with state := masks } : Activation).Valid world := ⟨ha.1, _, middleFrame⟩
                have context := Activation.context_spec middleValid slot hrest
                have alive : AliveOn world.live ((remainder.reads ++ suspended.reads) ++ [binding.address]) := by
                  intro a hm
                  rcases List.mem_append.mp hm with hm | hm
                  · rcases List.mem_append.mp hm with hm | hm
                    · exact context.alive a hm
                    · exact callerFrame.alive a hm
                  · obtain ⟨_, _, _, _, _, covered⟩ := middleFrame.get hb
                    exact middleFrame.alive a (covered (List.mem_append_right _ hm))
                have readable := packets_readable graph (fun a hm => currentFrame.alive a (subset hm))
                have validCallers : ∀ a ∈ ({ active with state := masks } :: callers), a.Valid world := by
                  intro a hm
                  rcases List.mem_cons.mp hm with rfl | hm
                  · exact middleValid
                  · exact hc a hm
                have ready := hready current suspended packets masks hcurrent hsuspended hargs
                obtain ⟨_, packetRead, returnedValid, kept⟩ := hcallee world _ _ function packets returned packet inner
                  hw readable validCallers alive ready hrun
                obtain ⟨input, inputFoot, inputPerm⟩ := operands_owners ha args hargs
                have partition : (active.owners world ++ (callerOwners world callers ++ external)).Perm
                    (input ++ (callerOwners world ({ active with state := masks } :: callers) ++ external)) := by
                  simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using
                    inputPerm.append_right (callerOwners world callers ++ external)
                obtain ⟨output, outputFoot, outputFrame, outputCoverage⟩ := howns world _ _ function packets returned packet inner input external
                  hw validCallers readable alive ready inputFoot (hf.perm partition) (covered.perm partition) hrun
                have retained := kept.weaken (fun _ hm => List.mem_append_left _ hm)
                have context' := (context.weaken (fun _ hm => List.mem_append_left _ hm) (by
                  intro a hm
                  exact alive a (List.mem_append_left _ hm))).preserve retained
                have callers' := callerFrame.transport (retained.weaken (fun _ hm => List.mem_append_right _ hm))
                apply store_owner_resources (active := {active with state := masks}) returnedValid ha.1 context' callers'
                  (fun _ hm => List.mem_append_right _ hm) packetRead outputFoot _ _ hstore
                · simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using outputFrame
                · simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using outputCoverage

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
