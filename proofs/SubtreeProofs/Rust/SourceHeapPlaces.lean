module

public import SubtreeProofs.Rust.SourceHeapReachability
public import SubtreeProofs.Rust.SourcePartialReadback

/-! Address-preserving partial place reads, including inline local fields.
Every successful source read selects an actual cell and reference graph.
The resulting pointer root is among the starting root and traversed guards. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

def locatePath (memory : Memory) (cell : Cell) (pointer : Pointer) : List Projection → Option (Cell × Pointer)
  | [] => some (cell, pointer)
  | .deref :: rest => match cell with
    | .owned address => do locatePath memory (← memory[address]?) ⟨address, []⟩ rest
    | .shared address => do locatePath memory (← read memory address) address rest
    | _ => none
  | .field variant index :: rest => match cell with
    | .node _ tag cells => do
      if variant.all (· = tag) then locatePath memory (← cells[index]?) (pointer.field index) rest else none
    | _ => none

theorem PartialGraphFields.get {memory : Memory} {cells : List Cell} {parts : List Slot} {guards : List Nat}
    (h : PartialGraphFields memory cells parts guards) (index : Nat) {part : Slot} (hg : parts[index]? = some part) :
    ∃ cell selected, cells[index]? = some cell ∧ PartialGraph memory cell part selected ∧ selected ⊆ guards := by
  induction index generalizing cells parts guards with
  | zero => cases h with
    | nil => cases hg
    | cons first rest =>
      cases hg
      exact ⟨_, _, rfl, first, fun _ ha => List.mem_append_left _ ha⟩
  | succ index ih => cases h with
    | nil => cases hg
    | cons first rest =>
      obtain ⟨cell, selected, hc, hs, hsub⟩ := ih rest hg
      exact ⟨cell, selected, hc, hs, fun address ha => List.mem_append_right _ (hsub ha)⟩

theorem PartialGraph.locate {memory : Memory} {cell : Cell} {part selected : Slot} {guards : List Nat}
    (h : PartialGraph memory cell part guards) (pointer : Pointer) (hr : read memory pointer = some cell)
    (path : List Projection) (hs : part.get path = some selected) :
    ∃ found address used, locatePath memory cell pointer path = some (found, address) ∧
      read memory address = some found ∧ PartialGraph memory found selected used ∧
      used ++ [address.root] ⊆ guards ++ [pointer.root] := by
  induction path generalizing cell part guards pointer with
  | nil =>
    simp only [Slot.get, Option.some.injEq] at hs
    subst selected
    exact ⟨cell, pointer, guards, rfl, hr, h, List.Subset.refl _⟩
  | cons projection rest ih =>
    cases projection with
    | deref => cases h with
      | empty _ | boolean _ | number _ | node _ => simp only [Slot.get, reduceCtorEq] at hs
      | @owned address child part guards hc hp =>
        have hr' : read memory ⟨address, []⟩ = some child := by simp only [Heap.read, hc, bind, Option.bind, Heap.fields]
        obtain ⟨found, target, used, hl, ht, hg, hsub⟩ := ih hp ⟨address, []⟩ hr' hs
        refine ⟨found, target, used, ?_, ht, hg, ?_⟩
        · simpa only [locatePath, hc, bind, Option.bind] using hl
        · intro a ha
          exact List.mem_append_left _ (hsub ha)
      | @shared address value guards graph => cases graph with
        | shared hc hp =>
          obtain ⟨found, target, used, hl, ht, hg, hsub⟩ := ih hp.partial address hc hs
          refine ⟨found, target, used, ?_, ht, hg, ?_⟩
          · simpa only [locatePath, hc, bind, Option.bind] using hl
          · intro a ha
            exact List.mem_append_left _ (hsub ha)
    | field variant index => cases h with
      | empty _ | boolean _ | number _ | shared _ | owned _ _ => simp only [Slot.get, reduceCtorEq] at hs
      | @node kind tag cells parts guards hf =>
        simp only [Slot.get] at hs
        split at hs
        next hv =>
          cases hg : parts[index]? with
          | none => simp [hg] at hs
          | some child =>
            obtain ⟨raw, selectedGuards, hc, hp, hsub⟩ := hf.get index hg
            have hr' : read memory (pointer.field index) = some raw := (read_field hr).trans hc
            obtain ⟨found, address, used, hl, ht, hh, hused⟩ := ih hp (pointer.field index) hr' (by simpa only [hg, bind, Option.bind] using hs)
            refine ⟨found, address, used, ?_, ht, hh, ?_⟩
            · simpa only [locatePath, hv, ite_true, hc, bind, Option.bind] using hl
            · intro a ha
              rcases List.mem_append.mp (hused ha) with ha | ha
              · exact List.mem_append_left _ (hsub ha)
              · exact List.mem_append_right _ ha
        next => contradiction

theorem PartialGraph.read {memory : Memory} {cell : Cell} {part : Slot} {guards : List Nat}
    (h : PartialGraph memory cell part guards) (pointer : Pointer) (hr : read memory pointer = some cell)
    (path : List Projection) {value : Value} (hs : part.read path = some value) :
    ∃ found address used, locatePath memory cell pointer path = some (found, address) ∧
      read memory address = some found ∧ Graph memory found value used ∧
      used ++ [address.root] ⊆ guards ++ [pointer.root] := by
  simp only [Slot.read] at hs
  cases hg : part.get path with
  | none => simp [hg] at hs
  | some selected =>
    have hm : selected.materialize = some value := by simpa only [hg, bind, Option.bind] using hs
    obtain ⟨found, address, used, hl, ht, hh, hsub⟩ := h.locate pointer hr path hg
    exact ⟨found, address, used, hl, ht, hh.materialize hm, hsub⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
