module

public import SubtreeProofs.Rust.SourceOwnerPackets

/-! Complete concrete reads partition into owner occurrences, shared-loan
occurrences and local stack roots. Multiplicity is retained, including aliased
shared reads. This identifies the semantic permissions needed for forward steps. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

mutual
  theorem BorrowFootprint.read_partition {memory : Memory} {cell : Cell} {part : Slot} {loans reads owners : List Nat}
      (h : BorrowFootprint memory cell part loans) (hg : PartialGraph memory cell part reads)
      (ho : Rep memory cell part owners) : reads.Perm (owners ++ loans) := by
    cases h with
    | empty _ => cases hg; cases ho; simp
    | boolean _ => cases hg; cases ho; simp
    | number _ => cases hg; cases ho; simp
    | node fields => cases hg with | node data => cases ho with
      | node owned => exact fields.read_partition data owned
    | shared loan => cases hg with | shared data => cases ho with
      | shared _ => simpa only [List.nil_append] using (loan.guards_unique data).symm ▸ List.Perm.refl reads
    | owned hr child => cases hg with | owned hs data => cases ho with
      | owned ht owned =>
        cases Option.some.inj (hr.symm.trans hs)
        cases Option.some.inj (hr.symm.trans ht)
        rename_i address cell part reads owners
        have first := (child.read_partition data owned).append_right [address]
        have swap := (List.perm_append_comm : (loans ++ [address]).Perm ([address] ++ loans)).append_left owners
        exact first.trans (by simpa only [List.append_assoc] using swap)
  termination_by sizeOf part

  theorem BorrowFields.read_partition {memory : Memory} {cells : List Cell} {parts : List Slot} {loans reads owners : List Nat}
      (h : BorrowFields memory cells parts loans) (hg : PartialGraphFields memory cells parts reads)
      (ho : FieldsRep memory cells parts owners) : reads.Perm (owners ++ loans) := by
    cases h with
    | nil => cases hg; cases ho; simp
    | cons first rest => cases hg with | cons data tail => cases ho with
      | cons owned more =>
        rename_i cell part cells parts firstLoans restLoans firstReads restReads firstOwners restOwners
        have combined := (first.read_partition data owned).append (rest.read_partition tail more)
        have swap := (List.perm_append_comm_assoc firstLoans restOwners restLoans).append_left firstOwners
        exact combined.trans (by simpa only [List.append_assoc] using swap)
  termination_by sizeOf parts
end

theorem ResourceRep.read_partition {memory : Memory} {cell : Cell} {part : Slot} {r : Resources}
    (h : ResourceRep memory cell part r) : r.reads.Perm (r.owners ++ r.loans) :=
  h.borrowed.read_partition h.graph h.owned

namespace Storage

theorem LocalResources.read_cases {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals} {r : Resources}
    (h : LocalResources world frame roots state slot r) {address : Nat} (hr : address ∈ r.reads) :
    address ∈ r.owners ∨ address ∈ r.loans ∨ ∃ binding, roots slot = some binding ∧ address = binding.address := by
  cases h with
  | vacant _ _ => cases hr
  | @stored binding cell resources hb _ _ hv _ =>
    rcases List.mem_append.mp hr with hr | hr
    · rcases List.mem_append.mp (hv.read_partition.subset hr) with ho | hl
      · exact Or.inl ho
      · exact Or.inr (Or.inl hl)
    · exact Or.inr (Or.inr ⟨binding, hb, List.mem_singleton.mp hr⟩)

theorem Inventory.read_cases {world : World} {frame : Nat} {roots : Roots} {state : Partial.Locals}
    {slots : List Nat} {r : Resources} (h : Inventory world frame roots state slots r)
    {address : Nat} (hr : address ∈ r.reads) :
    address ∈ r.owners ∨ address ∈ r.loans ∨
      ∃ slot ∈ slots, ∃ binding, roots slot = some binding ∧ address = binding.address := by
  induction h with
  | nil => cases hr
  | cons first rest ih =>
    rcases List.mem_append.mp hr with hr | hr
    · rcases first.read_cases hr with ho | hl | ⟨binding, hb, he⟩
      · exact Or.inl (List.mem_append_left _ ho)
      · exact Or.inr (Or.inl (List.mem_append_left _ hl))
      · exact Or.inr (Or.inr ⟨_, by simp, binding, hb, he⟩)
    · rcases ih hr with ho | hl | ⟨slot, hs, binding, hb, he⟩
      · exact Or.inl (List.mem_append_right _ ho)
      · exact Or.inr (Or.inl (List.mem_append_right _ hl))
      · exact Or.inr (Or.inr ⟨slot, List.mem_cons_of_mem _ hs, binding, hb, he⟩)

theorem Callers.read_cases {world : World} {callers : List Activation} {r : Resources}
    (h : Callers world callers r) {address : Nat} (hr : address ∈ r.reads) :
    address ∈ r.owners ∨ address ∈ r.loans ∨
      ∃ active ∈ callers, ∃ slot binding, active.roots slot = some binding ∧ address = binding.address := by
  induction h with
  | nil => cases hr
  | cons first rest ih =>
    rcases List.mem_append.mp hr with hr | hr
    · rcases first.inventory.read_cases hr with ho | hl | ⟨slot, _, binding, hb, he⟩
      · exact Or.inl (List.mem_append_left _ ho)
      · exact Or.inr (Or.inl (List.mem_append_left _ hl))
      · exact Or.inr (Or.inr ⟨_, by simp, slot, binding, hb, he⟩)
    · rcases ih hr with ho | hl | ⟨active, ha, slot, binding, hb, he⟩
      · exact Or.inl (List.mem_append_right _ ho)
      · exact Or.inr (Or.inl (List.mem_append_right _ hl))
      · exact Or.inr (Or.inr ⟨active, List.mem_cons_of_mem _ ha, slot, binding, hb, he⟩)

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed
