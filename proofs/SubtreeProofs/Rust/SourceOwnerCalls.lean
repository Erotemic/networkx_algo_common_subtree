module

public import SubtreeProofs.Rust.SourceOwnerAssignments
public import SubtreeProofs.Rust.SourceEvalDerivedCalls

/-! The actual callee receives a disjoint owned argument packet and the real
post-argument suspended frames. This proves the input ownership boundary;
callee result/retirement/allocation transfer is a separate contract. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

def BoxCoverage (world : World) (owners : List Nat) : Prop :=
  ∀ address, world.classes address = some .box → world.live address = true → address ∈ owners

theorem BoxCoverage.perm {world : World} {before after : List Nat} (h : BoxCoverage world before) (hp : before.Perm after) :
    BoxCoverage world after := fun a hc hl => hp.subset (h a hc hl)

theorem Callers.owners_preserved {before after : World} {callers : List Activation} {r : Resources}
    (h₁ : Callers before callers r) (h₂ : Callers after callers r) : callerOwners before callers = callerOwners after callers :=
  h₁.owners.trans h₂.owners.symm

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed.Derived

open LookupSource Heap LookupSource.Partial LookupSource.Partial.Addressed Storage

theorem assign_box_coverage {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) {slot : Nat} {rhs : Expr} {external : List Nat}
    (covered : BoxCoverage world (active.owners world ++ external))
    (h : assign world active callers slot rhs = some (final, after)) : BoxCoverage final (after.owners final ++ external) := by
  obtain ⟨hp, hc, hl⟩ := assign_owners ha h
  intro a hclass halive
  rw [hc] at hclass
  rw [hl] at halive
  exact (hp.append_right external).subset (covered a hclass halive)

theorem assign_caller_owner_frame {world final : World} {active after : Activation} {callers : List Activation}
    (ha : active.Valid world) (hc : ∀ a ∈ callers, a.Valid world) (hw : world.WellFormed)
    {slot : Nat} {rhs : Expr} {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : assign world active callers slot rhs = some (final, after)) :
    OwnerFrame final (after.owners final ++ (callerOwners final callers ++ external)) := by
  have actual := assign_spec ha hc hw (fun _ _ => none) slot rhs h
  obtain ⟨r, hs, hpost, _⟩ := actual.2.2.2.2.2.2.2
  have kept := (scanCallers_spec hc hs).owners_preserved hpost
  rw [← kept]
  exact assign_owner_frame ha hf h

theorem call_argument_owner_frame {callee : Callees} {world final : World} {active after : Activation}
    {callers : List Activation} {function : Function} {args : List Operand} {slot : Nat} {cost : Cost}
    (ha : active.Valid world) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    (h : call callee world active callers function args slot = some (final, after, cost)) :
    ∃ current suspended packets masks remainder binding middle returned work owners,
      active.scan world = some current ∧ scanCallers world callers = some suspended ∧
      Addressed.operands world active.roots (current.loans ++ suspended.reads) active.state args = some (packets, masks) ∧
      ({ active with state := masks } : Activation).scanExcept world slot = some remainder ∧
      active.roots slot = some binding ∧
      callee world ((remainder.reads ++ suspended.reads) ++ [binding.address])
        ({ active with state := masks } :: callers) function packets = some (middle, returned, work) ∧
      FieldsFootprint world.memory (packets.map Prod.fst) owners ∧
      OwnerFrame world (owners ++ (callerOwners world ({ active with state := masks } :: callers) ++ external)) := by
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
          | none => simp_all only [Bind.bind, Option.bind, reduceCtorEq]
          | some binding =>
            simp only [hcurrent, hsuspended, hargs, hrest, hb, Bind.bind, Option.bind] at h
            cases hcallee : callee world ((remainder.reads ++ suspended.reads) ++ [binding.address])
                ({ active with state := masks } :: callers) function packets with
            | none => simp only [hcallee, reduceCtorEq] at h
            | some result =>
              rcases result with ⟨middle, returned, work⟩
              obtain ⟨owners, ho, hframe⟩ := operands_owner_frame ha args hf hargs
              refine ⟨current, suspended, packets, masks, remainder, binding, middle, returned, work, owners,
                rfl, rfl, hargs, hrest, rfl, hcallee, ho, ?_⟩
              simpa only [callerOwners, List.flatMap_cons, List.append_assoc] using hframe

end SubtreeProofs.Rust.SourceEval.Addressed.Derived
