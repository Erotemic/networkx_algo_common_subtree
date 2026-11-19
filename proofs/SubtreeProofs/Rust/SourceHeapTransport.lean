module

public import SubtreeProofs.Rust.SourceHeapReachability

/-! Transport finite reference graphs across changes outside their read roots.
Unlike immutable extension, this permits in-place writes to unrelated storage.
The existing graph records shared targets transitively, so a protected outer
pointer cannot conceal a changed nested referent. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

def Retains (before after : Memory) (guards : List Nat) : Prop :=
  ∀ address ∈ guards, ∀ cell, before[address]? = some cell → after[address]? = some cell

theorem Retains.refl (memory : Memory) (guards : List Nat) : Retains memory memory guards :=
  fun _ _ _ h => h

theorem Retains.of_extends {before after : Memory} (h : Extends before after) (guards : List Nat) :
    Retains before after guards := fun a _ cell hr => h a cell hr

theorem Retains.weaken {before after : Memory} {guards smaller : List Nat} (h : Retains before after guards)
    (hs : smaller ⊆ guards) : Retains before after smaller := fun a ha => h a (hs ha)

theorem Retains.trans {first second third : Memory} {guards : List Nat}
    (h₁ : Retains first second guards) (h₂ : Retains second third guards) : Retains first third guards :=
  fun a ha cell hr => h₂ a ha cell (h₁ a ha cell hr)

theorem Retains.read {before after : Memory} {guards : List Nat} (h : Retains before after guards)
    {pointer : Pointer} (hg : pointer.root ∈ guards) {cell : Cell} (hr : read before pointer = some cell) :
    read after pointer = some cell := by
  unfold Heap.read at hr ⊢
  cases hc : before[pointer.root]? with
  | none => simp [hc] at hr
  | some stored => simpa only [h _ hg _ hc, bind, Option.bind] using
      (by simpa only [hc, bind, Option.bind] using hr : fields stored pointer.path = some cell)

mutual
  theorem Graph.transport {before after : Memory} {cell : Cell} {value : Value} {guards : List Nat}
      (h : Graph before cell value guards) (hk : Retains before after guards) : Graph after cell value guards := by
    cases h with
    | boolean b => exact .boolean b
    | number n => exact .number n
    | node fields => exact .node (fields.transport hk)
    | shared hr child =>
      exact .shared (hk.read (List.mem_append_right _ (by simp)) hr)
        (child.transport (hk.weaken (fun _ ha => List.mem_append_left _ ha)))
    | owned hr child =>
      exact .owned (hk _ (List.mem_append_right _ (by simp)) _ hr)
        (child.transport (hk.weaken (fun _ ha => List.mem_append_left _ ha)))

  theorem GraphFields.transport {before after : Memory} {cells : List Cell} {values : List Value} {guards : List Nat}
      (h : GraphFields before cells values guards) (hk : Retains before after guards) :
      GraphFields after cells values guards := by
    cases h with
    | nil => exact .nil
    | cons first rest =>
      exact .cons
        (first.transport (hk.weaken (fun _ ha => List.mem_append_left _ ha)))
        (rest.transport (hk.weaken (fun _ ha => List.mem_append_right _ ha)))
end

mutual
  theorem PartialGraph.transport {before after : Memory} {cell : Cell} {part : Slot} {guards : List Nat}
      (h : PartialGraph before cell part guards) (hk : Retains before after guards) : PartialGraph after cell part guards := by
    cases h with
    | empty cell => exact .empty cell
    | boolean b => exact .boolean b
    | number n => exact .number n
    | node fields => exact .node (fields.transport hk)
    | shared hg => exact .shared (hg.transport hk)
    | owned hr child =>
      exact .owned (hk _ (List.mem_append_right _ (by simp)) _ hr)
        (child.transport (hk.weaken (fun _ ha => List.mem_append_left _ ha)))

  theorem PartialGraphFields.transport {before after : Memory} {cells : List Cell} {parts : List Slot} {guards : List Nat}
      (h : PartialGraphFields before cells parts guards) (hk : Retains before after guards) :
      PartialGraphFields after cells parts guards := by
    cases h with
    | nil => exact .nil
    | cons first rest =>
      exact .cons
        (first.transport (hk.weaken (fun _ ha => List.mem_append_left _ ha)))
        (rest.transport (hk.weaken (fun _ ha => List.mem_append_right _ ha)))
end

mutual
  theorem PartialGraph.owner_transport {before after : Memory} {cell : Cell} {part : Slot} {guards owners : List Nat}
      (h : PartialGraph before cell part guards) (ho : Rep before cell part owners) (hk : Retains before after guards) :
      Rep after cell part owners := by
    cases h with
    | empty cell => cases ho; exact .empty cell
    | boolean b => cases ho; exact .boolean b
    | number n => cases ho; exact .number n
    | node fields => cases ho with
      | node owned => exact .node (fields.owner_transport owned hk)
    | shared hg => cases ho with
      | shared _ => exact .shared (hg.transport hk).represents
    | owned hr child => cases ho with
      | owned hr' owned =>
        have he := Option.some.inj (hr.symm.trans hr')
        cases he
        exact .owned (hk _ (List.mem_append_right _ (by simp)) _ hr)
          (child.owner_transport owned (hk.weaken (fun _ ha => List.mem_append_left _ ha)))

  theorem PartialGraphFields.owner_transport {before after : Memory} {cells : List Cell} {parts : List Slot}
      {guards owners : List Nat} (h : PartialGraphFields before cells parts guards)
      (ho : FieldsRep before cells parts owners) (hk : Retains before after guards) : FieldsRep after cells parts owners := by
    cases h with
    | nil => cases ho; exact .nil
    | cons first rest => cases ho with
      | cons a b =>
        exact .cons
          (first.owner_transport a (hk.weaken (fun _ ha => List.mem_append_left _ ha)))
          (rest.owner_transport b (hk.weaken (fun _ ha => List.mem_append_right _ ha)))
end

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
