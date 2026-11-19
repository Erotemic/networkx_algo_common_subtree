module

public import SubtreeProofs.Rust.SourceOwnerUpdates
public import SubtreeProofs.Rust.SourceEvalDerivedAssignments

/-! Successful guarded result storage preserves the exact packet/context owner
partition. One-pass derived assignment therefore conserves every initialized
owner occurrence, including partial Box shells and actual temporary RHS cells.
No post-RHS frame or guard list is supplied to the derived assignment theorem. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem store_owners {world final : World} {active : Activation} {slot : Nat} {retained contextGuards owners : List Nat}
    {packet : ValueCell} {after : State}
    (bound : Bounded active.roots active.count)
    (context : Frame world active.frame (active.roots.set slot none) (active.state.set slot .empty) contextGuards)
    (covered : contextGuards ⊆ retained)
    (hp : Readable world.memory world.live packet.1 packet.2) (ho : Footprint world.memory packet.1 owners)
    (h : store world active.roots active.frame slot retained active.state packet = some (final, after)) :
    (({ active with state := after } : Activation).owners final).Perm (owners ++ active.owners world) ∧
      final.classes = world.classes ∧ final.live = world.live := by
  rcases packet with ⟨cell, value⟩
  obtain ⟨used, hg, _⟩ := hp
  unfold store at h
  by_cases hempty : emptySlot (active.state slot) = true
  · have he := (emptySlot_iff _).mp hempty
    cases hb : active.roots slot with
    | none => simp [hempty, hb] at h
    | some binding =>
      cases hw : world.writeStack active.frame slot binding (retained ++ used) cell with
      | none => simp [hempty, hb, hg.trace, hw] at h
      | some next =>
        simp only [hempty, hb, hg.trace, hw, Bind.bind, Option.bind, ite_true, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨_, _, hbound, hsep, rfl⟩ := World.writeStack_iff.mp hw
        have hs : slot < active.count := by
          by_contra hn
          have hz := bound slot (by omega)
          rw [hb] at hz
          cases hz
        have kept := world.write_preserves hsep cell
        have packetRep := hg.partial.owner_transport (Rep.of_full hg.represents ho)
          (kept.reads.weaken (fun _ ha => List.mem_append_right _ ha))
        have hcell := (world.write_spec hbound cell).1
        have localRep : LocalRep (world.write binding.address cell).memory
            (rawAt (world.write binding.address cell) active.roots slot)
            ((active.state.set slot (Slot.ofValue value)) slot) owners := by
          simpa only [rawAt, hb, hcell, Partial.Locals.set, ite_true, Bind.bind, Option.bind] using LocalRep.stored packetRep
        have partition := Activation.owners_partition ({ active with state := active.state.set slot (Slot.ofValue value) } : Activation)
          (world.write binding.address cell) slot hs localRep.ownerList
        have stable : (active.withoutLocal slot).owners (world.write binding.address cell) = (active.withoutLocal slot).owners world := by
          change (Addressed.ownerState (world.write binding.address cell).memory
            (rawAt (world.write binding.address cell) (active.roots.set slot none)) (active.state.set slot .empty)).collect (List.range active.count) = _
          rw [context.ownerState_preserve (kept.weaken (fun _ ha => List.mem_append_left _ (covered ha)))]
          rfl
        refine ⟨?_, rfl, rfl⟩
        simpa only [Activation.withoutLocal_set, stable, Activation.withoutLocal_empty_owners active world slot he] using partition
  · simp [hempty] at h

theorem assign_owners {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) {slot : Nat} {rhs : Expr}
    (h : assign world active callers slot rhs = some (final, after)) :
    (active.owners world).Perm (after.owners final) ∧ final.classes = world.classes ∧ final.live = world.live := by
  unfold assign at h
  cases hcurrent : active.scan world with
  | none => simp [hcurrent] at h
  | some current =>
    cases hsuspended : scanCallers world callers with
    | none => simp [hcurrent, hsuspended] at h
    | some suspended =>
      cases he : Addressed.expression world active.roots (current.loans ++ suspended.reads) active.state rhs with
      | none => simp [hcurrent, hsuspended, he] at h
      | some pair =>
        rcases pair with ⟨packet, middle⟩
        cases hr : ({ active with state := middle } : Activation).scanExcept world slot with
        | none => simp [hcurrent, hsuspended, he, hr] at h
        | some remainder =>
          cases hs : store world active.roots active.frame slot (remainder.reads ++ suspended.reads) middle packet with
          | none => simp [hcurrent, hsuspended, he, hr, hs] at h
          | some pair =>
            rcases pair with ⟨next, masks⟩
            simp only [hcurrent, hsuspended, he, hr, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            obtain ⟨owners, ho, partition⟩ := expression_owners ha he
            have scanned := Activation.scan_spec ha hcurrent
            obtain ⟨_, hread, _, _, hmid⟩ := expression_spec scanned.frame he
            have midValid : ({ active with state := middle } : Activation).Valid world := ⟨scanned.bounded, current.reads, hmid⟩
            have context := Activation.context_spec midValid slot hr
            have packetLive := expression_readable scanned.frame he
            obtain ⟨stored, hclasses, hlive⟩ := store_owners (active := { active with state := middle })
              scanned.bounded context (fun _ ha => List.mem_append_left _ ha) packetLive.2.1 ho hs
            exact ⟨partition.trans stored.symm, hclasses, hlive⟩

theorem assign_owner_frame {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) {slot : Nat} {rhs : Expr} {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ external))
    (h : assign world active callers slot rhs = some (final, after)) :
    OwnerFrame final (after.owners final ++ external) := by
  obtain ⟨hp, hc, hl⟩ := assign_owners ha h
  exact ⟨(hp.append_right external).nodup_iff.mp hf.unique,
    fun a ha => by rw [hc]; exact hf.classified a ((hp.append_right external).symm.subset ha),
    fun a ha => by rw [hl]; exact hf.alive a ((hp.append_right external).symm.subset ha)⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
