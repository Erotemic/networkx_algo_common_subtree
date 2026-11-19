module

public import SubtreeProofs.Rust.SourceOwnerMoves
public import SubtreeProofs.Rust.SourceEvalDerivedDrop

/-! Temporary argument/RHS packets retain complete ownership occurrences.
Finite activation owners partition exactly into extracted packets and remaining
initialized locals. Shared reference reads may alias; they add no owners. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

structure OwnerFrame (world : World) (owners : List Nat) : Prop where
  unique : owners.Nodup
  classified : BoxOwners world owners
  alive : AliveOn world.live owners

theorem OwnerFrame.perm {world : World} {before after : List Nat} (h : OwnerFrame world before) (hp : before.Perm after) :
    OwnerFrame world after :=
  ⟨hp.nodup_iff.mp h.unique, fun a ha => h.classified a (hp.symm.subset ha), fun a ha => h.alive a (hp.symm.subset ha)⟩

def callerOwners (world : World) (callers : List Activation) : List Nat :=
  callers.flatMap (fun active => active.owners world)

theorem Callers.owners {world : World} {callers : List Activation} {r : Resources} (h : Callers world callers r) :
    callerOwners world callers = r.owners := by
  induction h with
  | nil => rfl
  | @cons active stack head tail first rest ih =>
    change active.owners world ++ callerOwners world stack = head.owners ++ tail.owners
    exact congrArg₂ List.append first.inventory.owners ih

theorem Inventory.owners_subset_reads {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r) : r.owners ⊆ r.reads := by
  induction h with
  | nil => simp
  | cons first rest ih =>
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact List.mem_append_left _ (first.owners_subset_reads ha)
    · exact List.mem_append_right _ (ih ha)

theorem Activation.owners_alive {world : World} {active : Activation} (h : active.Valid world) : AliveOn world.live (active.owners world) := by
  obtain ⟨r, hs, hr⟩ := active.scan_complete h
  rw [active.scan_owners h hs]
  exact fun a ha => hr.inventory.alive a (hr.inventory.owners_subset_reads ha)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem operands_owners {world : World} {active : Activation} (ha : active.Valid world)
    {guarded : List Nat} (ops : List Operand) {packets : List ValueCell} {after : State}
    (h : operands world active.roots guarded active.state ops = some (packets, after)) :
    ∃ owners, FieldsFootprint world.memory (packets.map Prod.fst) owners ∧
      (active.owners world).Perm (owners ++ ({ active with state := after } : Activation).owners world) := by
  induction ops generalizing active packets after with
  | nil => cases h; exact ⟨[], .nil, by simp⟩
  | cons op rest ih =>
    cases ho : operand world active.roots guarded active.state op with
    | none => simp [operands, ho] at h
    | some pair =>
      rcases pair with ⟨packet, middle⟩
      cases ht : operands world active.roots guarded middle rest with
      | none => simp [operands, ho, ht] at h
      | some pair =>
        rcases pair with ⟨tail, final⟩
        simp only [operands, ho, ht, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨first, hf, hp⟩ := operand_owners ha ho
        obtain ⟨bound, guards, frame⟩ := ha
        obtain ⟨_, _, _, _, hm⟩ := operand_spec frame ho
        have hmid : ({ active with state := middle } : Activation).Valid world := ⟨bound, guards, hm⟩
        obtain ⟨last, hl, hs⟩ := ih hmid ht
        exact ⟨first ++ last, .cons hf hl, by simpa only [List.append_assoc] using hp.trans (hs.append_left first)⟩

theorem expression_owners {world : World} {active : Activation} (ha : active.Valid world)
    {guarded : List Nat} {rhs : Expr} {packet : ValueCell} {after : State}
    (h : expression world active.roots guarded active.state rhs = some (packet, after)) :
    ∃ owners, Footprint world.memory packet.1 owners ∧
      (active.owners world).Perm (owners ++ ({ active with state := after } : Activation).owners world) := by
  cases rhs with
  | use op => exact operand_owners ha h
  | address place =>
    obtain ⟨_, guards, hf⟩ := ha
    cases hr : active.state.read place with
    | none => simp [expression, hr] at h
    | some value =>
      obtain ⟨pointer, used, hb, _, _⟩ := hf.borrow place hr
      simp only [expression, hr, hb, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨[], .shared pointer, by simp⟩
  | aggregate kind tag ops =>
    cases hs : operands world active.roots guarded active.state ops with
    | none => simp [expression, hs] at h
    | some pair =>
      rcases pair with ⟨cells, masks⟩
      simp only [expression, hs, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      obtain ⟨owners, ho, hp⟩ := operands_owners ha ops hs
      exact ⟨owners, .node ho, hp⟩
  | less left right =>
    cases hl : operand world active.roots guarded active.state left with
    | none => simp [expression, hl] at h
    | some pair =>
      rcases pair with ⟨⟨first, firstValue⟩, middle⟩
      cases hr : operand world active.roots guarded middle right with
      | none => simp [expression, hl, hr] at h
      | some pair =>
        rcases pair with ⟨⟨last, lastValue⟩, masks⟩
        obtain ⟨a, hfirst, hp⟩ := operand_owners ha hl
        obtain ⟨bound, guards, hf⟩ := ha
        obtain ⟨_, _, _, _, hmid⟩ := operand_spec hf hl
        have hm : ({ active with state := middle } : Activation).Valid world := ⟨bound, guards, hmid⟩
        obtain ⟨b, hlast, ht⟩ := operand_owners hm hr
        cases first with
        | boolean _ | node _ _ _ | shared _ | owned _ => simp [expression, hl, hr] at h
        | number firstNumber =>
          cases last with
          | boolean _ | node _ _ _ | shared _ | owned _ => simp [expression, hl, hr] at h
          | number lastNumber =>
            cases hfirst
            cases hlast
            cases hc : less32 firstNumber lastNumber with
            | none => simp [expression, hl, hr, hc] at h
            | some answer =>
              simp only [expression, hl, hr, hc, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨[], .boolean answer, hp.trans ht⟩

theorem operand_owner_frame {world : World} {active : Activation} (ha : active.Valid world)
    {external guarded : List Nat} {op : Operand} {packet : ValueCell} {after : State}
    (hf : OwnerFrame world (active.owners world ++ external))
    (h : operand world active.roots guarded active.state op = some (packet, after)) :
    ∃ owners, Footprint world.memory packet.1 owners ∧
      OwnerFrame world (owners ++ (({ active with state := after } : Activation).owners world ++ external)) := by
  obtain ⟨owners, ho, hp⟩ := operand_owners ha h
  exact ⟨owners, ho, hf.perm (by simpa only [List.append_assoc] using hp.append_right external)⟩

theorem operands_owner_frame {world : World} {active : Activation} (ha : active.Valid world)
    {external guarded : List Nat} (ops : List Operand) {packets : List ValueCell} {after : State}
    (hf : OwnerFrame world (active.owners world ++ external))
    (h : operands world active.roots guarded active.state ops = some (packets, after)) :
    ∃ owners, FieldsFootprint world.memory (packets.map Prod.fst) owners ∧
      OwnerFrame world (owners ++ (({ active with state := after } : Activation).owners world ++ external)) := by
  obtain ⟨owners, ho, hp⟩ := operands_owners ha ops h
  exact ⟨owners, ho, hf.perm (by simpa only [List.append_assoc] using hp.append_right external)⟩

theorem expression_owner_frame {world : World} {active : Activation} (ha : active.Valid world)
    {external guarded : List Nat} {rhs : Expr} {packet : ValueCell} {after : State}
    (hf : OwnerFrame world (active.owners world ++ external))
    (h : expression world active.roots guarded active.state rhs = some (packet, after)) :
    ∃ owners, Footprint world.memory packet.1 owners ∧
      OwnerFrame world (owners ++ (({ active with state := after } : Activation).owners world ++ external)) := by
  obtain ⟨owners, ho, hp⟩ := expression_owners ha h
  exact ⟨owners, ho, hf.perm (by simpa only [List.append_assoc] using hp.append_right external)⟩

end SubtreeProofs.Rust.SourceEval.Addressed
