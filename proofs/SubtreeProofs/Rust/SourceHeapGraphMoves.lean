module

public import SubtreeProofs.Rust.SourceHeapPlaces
public import SubtreeProofs.Rust.SourcePartialHeapMoves

/-! Actual partial moves partition finite read graphs as well as ownership.
Read guards may repeat because shared aliases are permitted. Box shell roots
remain in the partial parent after moving a payload. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

theorem PartialGraphFields.focus {memory : Memory} {cells : List Cell} {parts : List Slot} {guards : List Nat}
    (h : PartialGraphFields memory cells parts guards) (index : Nat) {part : Slot} (hg : parts[index]? = some part) :
    ∃ cell first leading trailing, cells[index]? = some cell ∧ PartialGraph memory cell part first ∧
      guards = leading ++ first ++ trailing ∧
      ∀ after rest, PartialGraph memory cell after rest →
        PartialGraphFields memory cells (parts.set index after) (leading ++ rest ++ trailing) := by
  induction index generalizing cells parts guards with
  | zero => cases h with
    | nil => cases hg
    | cons first rest =>
      cases hg
      exact ⟨_, _, [], _, rfl, first, rfl, fun _ _ hh => .cons hh rest⟩
  | succ index ih => cases h with
    | nil => cases hg
    | @cons cell head cells parts front back first rest =>
      obtain ⟨selected, used, leading, trailing, hc, hp, he, update⟩ := ih rest hg
      refine ⟨selected, used, front ++ leading, trailing, hc, hp, ?_, ?_⟩
      · simp only [he, List.append_assoc]
      · intro after remaining hr
        simpa only [List.set_cons_succ, List.append_assoc] using PartialGraphFields.cons first (update after remaining hr)

theorem PartialGraph.take {memory : Memory} {cell : Cell} {part after : Slot} {guards : List Nat}
    (h : PartialGraph memory cell part guards) (path : List Projection) {value : Value}
    (ht : part.take path = some (value, after)) :
    ∃ moved first rest, ownedProjection memory cell path = some moved ∧ Graph memory moved value first ∧
      PartialGraph memory cell after rest ∧ guards.Perm (first ++ rest) := by
  induction path generalizing cell part guards after with
  | nil =>
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at ht
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      exact ⟨cell, guards, [], rfl, h.materialize hm, .empty cell, by simp⟩
  | cons projection rest ih =>
    cases projection with
    | deref => cases h with
      | empty _ | boolean _ | number _ | shared _ | node _ => simp only [Slot.take, reduceCtorEq] at ht
      | @owned address child part guards hr hc =>
        cases hp : part.take rest with
        | none => simp [Slot.take, hp] at ht
        | some pair =>
          rcases pair with ⟨result, remaining⟩
          simp only [Slot.take, hp, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
          obtain ⟨rfl, rfl⟩ := ht
          obtain ⟨moved, a, b, hm, hv, ha, hperm⟩ := ih hc hp
          refine ⟨moved, a, b ++ [address], ?_, hv, .owned hr ha, ?_⟩
          · simpa only [ownedProjection, hr, bind, Option.bind] using hm
          · simpa only [List.append_assoc] using hperm.append_right [address]
    | field variant index => cases h with
      | empty _ | boolean _ | number _ | shared _ | owned _ _ => simp only [Slot.take, reduceCtorEq] at ht
      | @node kind tag cells parts guards hf =>
        simp only [Slot.take] at ht
        split at ht
        next hv =>
          cases hg : parts[index]? with
          | none => simp [hg] at ht
          | some selected =>
            obtain ⟨raw, used, leading, trailing, hc, hp, he, update⟩ := hf.focus index hg
            cases hs : selected.take rest with
            | none => simp [hg, hs] at ht
            | some pair =>
              rcases pair with ⟨result, remaining⟩
              simp only [hg, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
              obtain ⟨rfl, rfl⟩ := ht
              obtain ⟨moved, a, b, hm, hvalue, hafter, hperm⟩ := ih hp hs
              refine ⟨moved, a, leading ++ b ++ trailing, ?_, hvalue, .node (update remaining b hafter), ?_⟩
              · simpa only [ownedProjection, hv, ite_true, hc, bind, Option.bind] using hm
              · rw [he]
                have hfirst := (hperm.append_left leading).append_right trailing
                have hlast : ((leading ++ (a ++ b)) ++ trailing).Perm (a ++ (leading ++ b ++ trailing)) := by
                  simpa only [List.append_assoc] using List.perm_append_comm_assoc leading a (b ++ trailing)
                exact hfirst.trans hlast
        next => cases ht

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
