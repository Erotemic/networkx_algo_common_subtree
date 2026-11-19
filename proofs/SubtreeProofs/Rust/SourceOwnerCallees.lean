module

public import SubtreeProofs.Rust.SourceOwnerHelperProfiles

/-! The actual eight-function helper dispatcher transfers complete owned input
packets into complete output packets and retains actual suspended/external owner
frames. Independent argument types supply its existing conservative profiles;
all successful fuels are covered, without native height hypotheses. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap Partial Partial.Addressed Storage

def CallsOwn (callee : Callees) : Prop :=
  ∀ world guards callers function packets final packet cost owners external,
    world.WellFormed → (∀ a ∈ callers, a.Valid world) →
    (∀ p ∈ packets, Readable world.memory world.live p.1 p.2) → AliveOn world.live guards →
    TypedReady world function packets → FieldsFootprint world.memory (packets.map Prod.fst) owners →
    OwnerFrame world (owners ++ (callerOwners world callers ++ external)) →
    BoxCoverage world (owners ++ (callerOwners world callers ++ external)) →
    callee world guards callers function packets = some (final, packet, cost) →
    ∃ output, Footprint final.memory packet.1 output ∧
      OwnerFrame final (output ++ (callerOwners final callers ++ external)) ∧
      BoxCoverage final (output ++ (callerOwners final callers ++ external))

end SubtreeProofs.Rust.SourceEval.Addressed.Derived

namespace SubtreeProofs.Rust.SourceEval.Addressed.Helpers

open LookupSource Heap Heap.Owners Partial Partial.Addressed Storage

theorem boxNew_owner_ledger {fuel : Nat} {world final : World} (hw : world.WellFormed)
    {packets : List ValueCell} {owners : List Nat} (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    {packet : ValueCell} {cost : Cost} (h : boxNew fuel world packets = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  unfold boxNew at h
  split at h
  next fuel cell value =>
    cases h
    obtain ⟨first, rest, rfl, hf, ht⟩ := ho.cons_inv
    cases ht
    have he := (world.allocate_spec .box cell).1
    refine ⟨first ++ [world.memory.length], ?_, ?_, he, World.allocate_boxSuffix hw cell⟩
    · exact .owned (world.allocate_spec .box cell).2.1 (Heap.Spatial.footprint_mono he hf)
    · simp [fresh, World.allocate]
  next => cases h

theorem numberOption_footprint (memory : Memory) (value : Option Nat) : Footprint memory (numberOptionCell value) [] := by
  cases value with
  | none => exact .node .nil
  | some n => exact .node (.cons (.number n) .nil)

theorem checkedAdd_owner_ledger {fuel : Nat} {world final : World} (hw : world.WellFormed)
    {packets : List ValueCell} {owners : List Nat} (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    {packet : ValueCell} {cost : Cost} (h : checkedAdd fuel world packets = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  unfold checkedAdd at h
  split at h
  next fuel left leftValue right rightValue =>
    split at h
    next bounds =>
      cases h
      cases ho with
      | cons first rest =>
        cases first
        cases rest with
        | cons second tail =>
          cases second
          cases tail
          exact ⟨[], numberOption_footprint _ _, by simp [fresh], .refl _, (World.boxSuffix_self hw).symm⟩
    next => cases h
  next => cases h

theorem callee_owner_ledger (fuel budget : Nat) {world final : World} (hw : world.WellFormed)
    (function : SourceEval.Function) (packets : List ValueCell)
    (hp : ∀ p ∈ packets, Readable world.memory world.live p.1 p.2)
    (typed : Derived.TypedReady world function packets) {owners : List Nat}
    (ho : FieldsFootprint world.memory (packets.map Prod.fst) owners)
    {guards : List Nat} {callers : List Activation} {packet : ValueCell} {cost : Cost}
    (h : callee fuel budget world guards callers function packets = some (final, packet, cost)) :
    ∃ result, Footprint final.memory packet.1 result ∧ result.Perm (owners ++ fresh world.memory final.memory) ∧
      Extends world.memory final.memory ∧ final = world.boxSuffix final.memory := by
  cases function with
  | copyWord => exact lookup_owner_ledger fuel budget hw .copyWord packets (typed_lookup_profile .copyWord (by decide) hp typed) ho h
  | compare => exact lookup_owner_ledger fuel budget hw .compare packets (typed_lookup_profile .compare (by decide) hp typed) ho h
  | copyResult => exact lookup_owner_ledger fuel budget hw .copyResult packets (typed_lookup_profile .copyResult (by decide) hp typed) ho h
  | lookup => exact lookup_owner_ledger fuel budget hw .lookup packets (typed_lookup_profile .lookup (by decide) hp typed) ho h
  | concatenate => exact memo_owner_ledger fuel budget hw .concatenate packets (typed_memo_profile .concatenate (by decide) hp typed) ho h
  | insert => exact memo_owner_ledger fuel budget hw .insert packets (typed_memo_profile .insert (by decide) hp typed) ho h
  | boxNew => exact boxNew_owner_ledger hw ho h
  | checkedAdd => exact checkedAdd_owner_ledger hw ho h
  | chooseLonger | evaluate | maximum => cases h

theorem callee_owns (fuel budget : Nat) : Derived.CallsOwn (callee fuel budget) := by
  intro world guards callers function packets final packet cost owners external hw hc hp hl typed ho hf covered h
  obtain ⟨output, hout, hperm, he, hshape⟩ := callee_owner_ledger fuel budget hw function packets hp typed ho h
  obtain ⟨r, _, hcallers⟩ := scanCallers_complete callers hc
  have hk := world.boxSuffix_keeps hw he r.reads
  rw [← hshape] at hk
  have retained := hcallers.owners_preserved (hcallers.transport hk.preserves)
  have resources := boxSuffix_owner_transfer hw he hperm hf covered
  rw [← hshape] at resources
  rw [← retained]
  exact ⟨output, hout, resources⟩

end SubtreeProofs.Rust.SourceEval.Addressed.Helpers
