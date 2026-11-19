module

public import SubtreeProofs.Rust.SourcePartialReadback
public import SubtreeProofs.Rust.LookupTypePrimitives

import all SubtreeProofs.Rust.SourcePartialValue
import all SubtreeProofs.Rust.SourcePartialMoves

/-! Independent partial-local typing. Holes retain their declared type;
constructor tags, field lists and owned Box shells retain their shape. A
successful read requires complete initialization of the selected subtree.
This is snapshot typing, not addressed loan or allocator safety. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

open Heap SourceTypes

mutual
  inductive SlotTyped : Slot → Ty → Prop where
    | empty (ty : Ty) : SlotTyped .empty ty
    | boolean (value : Bool) : SlotTyped (.boolean value) .boolean
    | number {value : Nat} : value < 2^32 → SlotTyped (.number value) .u32
    | node {kind : Kind} {variant : Nat} {fields : List Slot} {types : List Ty} {ty : Ty} :
        Shape kind variant types ty → FieldsSlotTyped fields types → SlotTyped (.node kind variant fields) ty
    | shared {target : Value} {ty : Ty} : SnapshotTyped target ty → SlotTyped (.shared target) (.shared ty)
    | owned {child : Slot} {ty : Ty} : SlotTyped child ty → SlotTyped (.boxed child) (.owned ty)

  inductive FieldsSlotTyped : List Slot → List Ty → Prop where
    | nil : FieldsSlotTyped [] []
    | cons {first : Slot} {ty : Ty} {rest : List Slot} {types : List Ty} :
        SlotTyped first ty → FieldsSlotTyped rest types → FieldsSlotTyped (first :: rest) (ty :: types)
end

mutual
  theorem ofValue_typed {value : Value} {ty : Ty} (h : SnapshotTyped value ty) :
      SlotTyped (Slot.ofValue value) ty :=
    match h with
    | .boolean b => by simpa only [Slot.ofValue] using (SlotTyped.boolean b)
    | .number hb => by simpa only [Slot.ofValue] using (SlotTyped.number hb)
    | .node hs hf => by simpa only [Slot.ofValue] using (SlotTyped.node hs (ofFields_typed hf))
    | .shared ht => by simpa only [Slot.ofValue] using (SlotTyped.shared ht)
    | .owned ht => by simpa only [Slot.ofValue] using (SlotTyped.owned (ofValue_typed ht))

  theorem ofFields_typed {values : List Value} {types : List Ty} (h : SnapshotFieldsTyped values types) :
      FieldsSlotTyped (ofFields values) types :=
    match h with
    | .nil => by simpa only [ofFields] using FieldsSlotTyped.nil
    | .cons first rest => by simpa only [ofFields] using (FieldsSlotTyped.cons (ofValue_typed first) (ofFields_typed rest))
end

mutual
  theorem SlotTyped.materialize {part : Slot} {ty : Ty} (h : SlotTyped part ty)
      {value : Value} (hr : part.materialize = some value) : SnapshotTyped value ty := by
    cases h with
    | empty => simp only [Slot.materialize, reduceCtorEq] at hr
    | boolean b =>
      simp only [Slot.materialize, Option.some.injEq] at hr
      cases hr
      exact .boolean b
    | number bound =>
      simp only [Slot.materialize, Option.some.injEq] at hr
      cases hr
      exact .number bound
    | shared ht =>
      simp only [Slot.materialize, Option.some.injEq] at hr
      cases hr
      exact .shared ht
    | @owned child inner ht =>
      cases hc : child.materialize with
      | none => simp [Slot.materialize, hc] at hr
      | some child =>
        simp only [Slot.materialize, hc, Functor.map, Option.map_some, Option.some.injEq] at hr
        subst value
        exact .owned (ht.materialize hc)
    | @node kind variant parts types ty hs hf =>
      cases hc : materializeFields parts with
      | none => simp [Slot.materialize, hc] at hr
      | some fields =>
        simp only [Slot.materialize, hc, Functor.map, Option.map_some, Option.some.injEq] at hr
        subst value
        exact .node hs (hf.materialize hc)

  theorem FieldsSlotTyped.materialize {parts : List Slot} {types : List Ty} (h : FieldsSlotTyped parts types)
      {values : List Value} (hr : materializeFields parts = some values) : SnapshotFieldsTyped values types := by
    cases h with
    | nil =>
      simp only [materializeFields, Option.some.injEq] at hr
      cases hr
      exact .nil
    | @cons part ty parts types ht hts =>
      cases hh : part.materialize with
      | none => simp [materializeFields, hh] at hr
      | some first =>
        cases ht' : materializeFields parts with
        | none => simp [materializeFields, hh, ht'] at hr
        | some rest =>
          simp only [materializeFields, hh, ht', bind, Option.bind, pure, Option.some.injEq] at hr
          subst values
          exact .cons (ht.materialize hh) (hts.materialize ht')
end

theorem FieldsSlotTyped.get {parts : List Slot} {types : List Ty} (h : FieldsSlotTyped parts types)
    (index : Nat) {part : Slot} {ty : Ty} (hp : parts[index]? = some part) (ht : types[index]? = some ty) :
    SlotTyped part ty := by
  induction index generalizing parts types with
  | zero => cases h with
    | nil => cases hp
    | cons first rest => cases hp; cases ht; exact first
  | succ index ih => cases h with
    | nil => cases hp
    | cons first rest => exact ih rest hp ht

theorem FieldsSlotTyped.set {parts : List Slot} {types : List Ty} (h : FieldsSlotTyped parts types)
    (index : Nat) {ty : Ty} {after : Slot} (ht : types[index]? = some ty) (ha : SlotTyped after ty) :
    FieldsSlotTyped (parts.set index after) types := by
  induction index generalizing parts types with
  | zero => cases h with
    | nil => cases ht
    | cons first rest => cases ht; exact .cons ha rest
  | succ index ih => cases h with
    | nil => cases ht
    | cons first rest => exact .cons first (ih rest ht)

def inferPath (ty : Ty) : List Projection → Option Ty
  | [] => some ty
  | .deref :: rest => do inferPath (← deref ty) rest
  | .field variant index :: rest => do inferPath (← fieldType ty variant index) rest

theorem SlotTyped.get {part : Slot} {ty : Ty} (h : SlotTyped part ty) (path : List Projection)
    {child : Slot} {target : Ty} (ht : inferPath ty path = some target) (hr : part.get path = some child) :
    SlotTyped child target := by
  induction path generalizing part ty child target with
  | nil => cases ht; cases hr; exact h
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases h with
      | empty => cases hr
      | boolean _ | number _ => cases hr
      | node hs hf => cases hr
      | shared hc =>
        simp only [inferPath, deref, bind, Option.bind] at ht
        exact ih (ofValue_typed hc) ht hr
      | owned hc =>
        simp only [inferPath, deref, bind, Option.bind] at ht
        exact ih hc ht hr
    | field variant index =>
      cases h with
      | empty => cases hr
      | boolean _ | number _ | shared _ | owned _ => cases hr
      | @node kind actual parts types ty hs hf =>
        simp only [Slot.get] at hr
        split at hr
        next hv =>
          cases hg : parts[index]? with
          | none => simp [hg] at hr
          | some selected =>
            cases hfTy : fieldType ty variant index with
            | none => simp [inferPath, hfTy] at ht
            | some fieldTy =>
              have hfield := hf.get index hg (projection_fields hs hv hfTy)
              exact ih hfield (by simpa only [inferPath, hfTy, bind, Option.bind] using ht)
                (by simpa only [hg, bind, Option.bind] using hr)
        next => cases hr

theorem SlotTyped.read {part : Slot} {ty : Ty} (h : SlotTyped part ty) (path : List Projection)
    {value : Value} {target : Ty} (ht : inferPath ty path = some target) (hr : part.read path = some value) :
    SnapshotTyped value target := by
  cases hg : part.get path with
  | none => simp [Slot.read, hg] at hr
  | some child => exact (h.get path ht hg).materialize (by simpa only [Slot.read, hg, bind, Option.bind] using hr)

theorem SlotTyped.take {part : Slot} {ty : Ty} (h : SlotTyped part ty) (path : List Projection)
    {value : Value} {after : Slot} {target : Ty}
    (ht : inferPath ty path = some target) (hr : part.take path = some (value, after)) :
    SnapshotTyped value target ∧ SlotTyped after ty := by
  induction path generalizing part ty after target with
  | nil =>
    cases ht
    cases hm : part.materialize with
    | none => simp [Slot.take, hm] at hr
    | some result =>
      simp only [Slot.take, hm, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      exact ⟨h.materialize hm, .empty _⟩
  | cons projection rest ih =>
    cases projection with
    | deref =>
      cases h with
      | empty => cases hr
      | boolean _ | number _ | shared _ | node _ _ => cases hr
      | @owned child inner hc =>
        cases htaken : child.take rest with
        | none => simp [Slot.take, htaken] at hr
        | some pair =>
          rcases pair with ⟨moved, remaining⟩
          simp only [Slot.take, htaken, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          have hh := ih hc (by simpa only [inferPath, deref, bind, Option.bind] using ht) htaken
          exact ⟨hh.1, .owned hh.2⟩
    | field variant index =>
      cases h with
      | empty => cases hr
      | boolean _ | number _ | shared _ | owned _ => cases hr
      | @node kind actual parts types ty hs hf =>
        simp only [Slot.take] at hr
        split at hr
        next hv =>
          cases hg : parts[index]? with
          | none => simp [hg] at hr
          | some selected =>
            cases hfTy : fieldType ty variant index with
            | none => simp [inferPath, hfTy] at ht
            | some fieldTy =>
              have hi := projection_fields hs hv hfTy
              have hfield := hf.get index hg hi
              cases htaken : selected.take rest with
              | none => simp [hg, htaken] at hr
              | some pair =>
                rcases pair with ⟨moved, remaining⟩
                simp only [hg, htaken, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
                obtain ⟨rfl, rfl⟩ := hr
                have hh := ih hfield (by simpa only [inferPath, hfTy, bind, Option.bind] using ht) htaken
                exact ⟨hh.1, .node hs (hf.set index hi hh.2)⟩
        next => cases hr

end SubtreeProofs.Rust.LookupSource.Partial
