module

public import SubtreeProofs.Rust.SourcePartialHeap
public import SubtreeProofs.Rust.SourcePartialTyping

/-! Address-preserving owned field moves. Stored cells remain unchanged while
initialization masks transfer their complete Box occurrence lists. Shared
referents cannot be moved through. Liveness and loan protection are separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

def ownedProjection (memory : Memory) (cell : Cell) : List Projection → Option Cell
  | [] => some cell
  | .deref :: rest => match cell with
    | .owned address => do ownedProjection memory (← memory[address]?) rest
    | _ => none
  | .field variant index :: rest => match cell with
    | .node _ actual cells => do
      if variant.all (· = actual) then ownedProjection memory (← cells[index]?) rest else none
    | _ => none

theorem FieldsRep.focus {memory : Memory} {cells : List Cell} {parts : List Slot} {owners : List Nat}
    (h : FieldsRep memory cells parts owners) (index : Nat) {part : Slot} (hg : parts[index]? = some part) :
    ∃ cell first leading trailing, cells[index]? = some cell ∧ Rep memory cell part first ∧
      owners = leading ++ first ++ trailing ∧
      ∀ after rest, Rep memory cell after rest →
        FieldsRep memory cells (parts.set index after) (leading ++ rest ++ trailing) := by
  induction index generalizing cells parts owners with
  | zero => cases h with
    | nil => cases hg
    | @cons cell part cells parts first rest hh ht =>
      cases hg
      refine ⟨cell, first, [], rest, rfl, hh, rfl, ?_⟩
      intro after remaining hr
      exact .cons hr ht
  | succ index ih => cases h with
    | nil => cases hg
    | @cons cell head cells parts first rest hh ht =>
      obtain ⟨selected, own, leading, trailing, hc, hp, he, update⟩ := ih ht hg
      refine ⟨selected, own, first ++ leading, trailing, hc, hp, ?_, ?_⟩
      · simp only [he, List.append_assoc]
      · intro after remaining hr
        simpa only [List.set_cons_succ, List.append_assoc] using FieldsRep.cons hh (update after remaining hr)

theorem Rep.take {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
    (h : Rep memory cell part owners) (path : List Projection) {value : Value} {after : Slot}
    (ht : part.take path = some (value, after)) :
    ∃ moved movedOwners remainingOwners,
      ownedProjection memory cell path = some moved ∧ Represents memory moved value ∧
      Footprint memory moved movedOwners ∧ Rep memory cell after remainingOwners ∧
      owners.Perm (movedOwners ++ remainingOwners) := by
  induction path generalizing cell part owners after with
  | nil =>
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at ht
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      have hv := h.materialize hm
      exact ⟨cell, owners, [], rfl, hv.1, hv.2, .empty cell, by simp⟩
  | cons projection rest ih =>
    cases projection with
    | deref => cases h with
      | empty _ | boolean _ | number _ | shared _ | node _ => simp only [Slot.take, reduceCtorEq] at ht
      | @owned address child part childOwners hr hc =>
        cases hp : part.take rest with
        | none => simp [Slot.take, hp] at ht
        | some pair =>
          rcases pair with ⟨result, remaining⟩
          simp only [Slot.take, hp, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          obtain ⟨moved, a, b, hm, hv, hf, ha, hperm⟩ := ih hc hp
          refine ⟨moved, a, b ++ [address], ?_, hv, hf, .owned hr ha, ?_⟩
          · simpa only [ownedProjection, hr, bind, Option.bind] using hm
          · simpa only [List.append_assoc] using hperm.append_right [address]
    | field variant index => cases h with
      | empty _ | boolean _ | number _ | shared _ | owned _ _ => simp only [Slot.take, reduceCtorEq] at ht
      | @node kind actual cells parts owners hf =>
        simp only [Slot.take] at ht
        split at ht
        next hv =>
          cases hg : parts[index]? with
          | none => simp [hg] at ht
          | some selected =>
            obtain ⟨raw, own, leading, trailing, hc, hp, he, update⟩ := hf.focus index hg
            cases hs : selected.take rest with
            | none => simp [hg, hs] at ht
            | some pair =>
              rcases pair with ⟨result, remaining⟩
              simp only [hg, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
              obtain ⟨rfl, rfl⟩ := ht
              obtain ⟨moved, a, b, hm, hvalue, hfoot, hafter, hperm⟩ := ih hp hs
              refine ⟨moved, a, leading ++ b ++ trailing, ?_, hvalue, hfoot, .node (update remaining b hafter), ?_⟩
              · simpa only [ownedProjection, hv, ite_true, hc, bind, Option.bind] using hm
              · rw [he]
                have hfirst := (hperm.append_left leading).append_right trailing
                have hlast : ((leading ++ (a ++ b)) ++ trailing).Perm (a ++ (leading ++ b ++ trailing)) := by
                  simpa only [List.append_assoc] using List.perm_append_comm_assoc leading a (b ++ trailing)
                exact hfirst.trans hlast
        next => cases ht

theorem Rep.take_typed {memory : Memory} {cell : Cell} {part after : Slot} {owners : List Nat}
    (h : Rep memory cell part owners) {ty target : Ty} (hpart : SlotTyped part ty) (path : List Projection)
    {value : Value} (hp : inferPath ty path = some target) (ht : part.take path = some (value, after)) :
    ∃ moved movedOwners remainingOwners,
      ownedProjection memory cell path = some moved ∧ Typed memory moved target ∧
      Footprint memory moved movedOwners ∧ Rep memory cell after remainingOwners ∧
      SlotTyped after ty ∧ owners.Perm (movedOwners ++ remainingOwners) := by
  obtain ⟨moved, a, b, hm, hv, hf, ha, hperm⟩ := h.take path ht
  have htyped := hpart.take path hp ht
  exact ⟨moved, a, b, hm, hv.typed htyped.1, hf, ha, htyped.2, hperm⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
