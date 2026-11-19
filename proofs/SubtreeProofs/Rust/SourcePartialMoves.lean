module

public import SubtreeProofs.Rust.SourcePartialValue

/-! Field moves preserve sibling initialization and exactly transfer the
selected value's destructor work. Moving through a shared reference is rejected;
moving an owned Box payload retains the Box shell for subsequent destruction. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

inductive Projection where
  | deref
  | field : Option Nat → Nat → Projection
  deriving DecidableEq, Repr

def Slot.get (part : Slot) : List Projection → Option Slot
  | [] => some part
  | .deref :: rest =>
    match part with
    | .boxed child => child.get rest
    | .shared target => (Slot.ofValue target).get rest
    | _ => none
  | .field variant index :: rest =>
    match part with
    | .node _ actual fields => do
      if variant.all (· = actual) then (← fields[index]?).get rest else none
    | _ => none

def Slot.read (part : Slot) (path : List Projection) : Option Value := do
  (← part.get path).materialize

def Slot.take (part : Slot) : List Projection → Option (Value × Slot)
  | [] => do
    let value ← part.materialize
    some (value, .empty)
  | .deref :: rest =>
    match part with
    | .boxed child => do
      let (value, after) ← child.take rest
      some (value, .boxed after)
    | _ => none
  | .field variant index :: rest =>
    match part with
    | .node kind actual fields => do
      if variant.all (· = actual) then
        let child ← fields[index]?
        let (value, after) ← child.take rest
        some (value, .node kind actual (fields.set index after))
      else none
    | _ => none

theorem DropWork.plus_left_comm (a b c : DropWork) : a.plus (b.plus c) = b.plus (a.plus c) := by
  cases a; cases b; cases c; simp [plus, Nat.add_left_comm]

theorem dropFields_set {fields : List Slot} {index : Nat} {before after : Slot} {moved : DropWork}
    (hget : fields[index]? = some before) (hwork : before.dropWork = moved.plus after.dropWork) :
    dropFields fields = moved.plus (dropFields (fields.set index after)) := by
  induction index generalizing fields with
  | zero =>
    cases fields with
    | nil => cases hget
    | cons first rest =>
      cases hget
      simp only [dropFields, List.set_cons_zero, hwork]
      exact DropWork.plus_assoc _ _ _
  | succ index ih =>
    cases fields with
    | nil => cases hget
    | cons first rest =>
      simp only [List.getElem?_cons_succ] at hget
      simp only [dropFields, List.set_cons_succ, ih hget]
      exact DropWork.plus_left_comm _ _ _

theorem Slot.take_read (part : Slot) (path : List Projection) {value : Value} {after : Slot}
    (ht : part.take path = some (value, after)) : part.read path = some value := by
  induction path generalizing part after with
  | nil =>
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at ht
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      simpa only [Slot.read, Slot.get, bind, Option.bind] using hm
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i child
      cases hc : child.take rest with
      | none => simp [hc] at ht
      | some pair =>
        rcases pair with ⟨result, remaining⟩
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simpa only [Slot.read, Slot.get] using ih child hc
    | field variant index =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i kind actual fields
      split at ht
      next hv =>
        cases hg : fields[index]? with
        | none => simp [hg] at ht
        | some child =>
          cases hc : child.take rest with
          | none => simp [hg, hc] at ht
          | some pair =>
            rcases pair with ⟨result, remaining⟩
            simp only [hg, hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            simpa only [Slot.read, Slot.get, hv, ite_true, hg, bind, Option.bind] using ih child hc
      next => cases ht

theorem Slot.take_work (part : Slot) (path : List Projection) {value : Value} {after : Slot}
    (ht : part.take path = some (value, after)) :
    part.dropWork = (Slot.ofValue value).dropWork.plus after.dropWork := by
  induction path generalizing part after with
  | nil =>
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at ht
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      rw [part.eq_of_materialize hm]
      simp only [Slot.dropWork, DropWork.plus_zero]
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i child
      cases hc : child.take rest with
      | none => simp [hc] at ht
      | some pair =>
        rcases pair with ⟨result, remaining⟩
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [Slot.dropWork, ih child hc]
        exact DropWork.plus_left_comm _ _ _
    | field variant index =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i kind actual fields
      split at ht
      next hv =>
        cases hg : fields[index]? with
        | none => simp [hg] at ht
        | some child =>
          cases hc : child.take rest with
          | none => simp [hg, hc] at ht
          | some pair =>
            rcases pair with ⟨result, remaining⟩
            simp only [hg, hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            simp only [Slot.dropWork, dropFields_set hg (ih child hc)]
            exact DropWork.plus_left_comm _ _ _
      next => cases ht

theorem Slot.take_hole (part : Slot) (path : List Projection) {value : Value} {after : Slot}
    (ht : part.take path = some (value, after)) : after.get path = some .empty := by
  induction path generalizing part after with
  | nil =>
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at ht
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
      obtain ⟨rfl, rfl⟩ := ht
      rfl
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i child
      cases hc : child.take rest with
      | none => simp [hc] at ht
      | some pair =>
        rcases pair with ⟨result, remaining⟩
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact ih child hc
    | field variant index =>
      cases part <;> simp only [Slot.take] at ht <;> try contradiction
      rename_i kind actual fields
      split at ht
      next hv =>
        cases hg : fields[index]? with
        | none => simp [hg] at ht
        | some child =>
          cases hc : child.take rest with
          | none => simp [hg, hc] at ht
          | some pair =>
            rcases pair with ⟨result, remaining⟩
            simp only [hg, hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
            obtain ⟨rfl, rfl⟩ := ht
            have hi : index < fields.length := (List.getElem?_eq_some_iff.mp hg).choose
            simpa only [Slot.get, hv, ite_true, List.getElem?_set_self hi, bind, Option.bind] using ih child hc
      next => cases ht

theorem Slot.take_otherField {kind : Kind} {actual : Nat} {fields : List Slot}
    {variant : Option Nat} {index : Nat} {rest : List Projection} {value : Value} {after : Slot}
    (ht : (Slot.node kind actual fields).take (.field variant index :: rest) = some (value, after))
    (otherVariant : Option Nat) (other : Nat) (suffix : List Projection) (hne : other ≠ index) :
    after.get (.field otherVariant other :: suffix) =
      (Slot.node kind actual fields).get (.field otherVariant other :: suffix) := by
  simp only [Slot.take] at ht
  split at ht
  next hv =>
    cases hg : fields[index]? with
    | none => simp [hg] at ht
    | some child =>
      cases hc : child.take rest with
      | none => simp [hg, hc] at ht
      | some pair =>
        rcases pair with ⟨result, remaining⟩
        simp only [hg, hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        simp only [Slot.get, List.getElem?_set, Ne.symm hne, ite_false]
  next => cases ht

end SubtreeProofs.Rust.LookupSource.Partial
