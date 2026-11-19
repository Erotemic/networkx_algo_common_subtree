module

public import SubtreeProofs.Rust.LookupSource
public import Mathlib.Data.List.Basic

/-! Partially initialized source values for actual field moves. Shared
referents remain read-only snapshots; holes are local initialization state,
not a new source value. This module does not claim addressed Rust adequacy. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial

inductive Slot where
  | empty
  | boolean : Bool → Slot
  | number : Nat → Slot
  | node : Kind → Nat → List Slot → Slot
  | shared : Value → Slot
  | boxed : Slot → Slot

mutual
  def Slot.ofValue : Value → Slot
    | .boolean value => .boolean value
    | .number value => .number value
    | .node kind variant fields => .node kind variant (ofFields fields)
    | .reference target => .shared target
    | .boxed child => .boxed (Slot.ofValue child)
  termination_by value => sizeOf value

  def ofFields : List Value → List Slot
    | [] => []
    | first :: rest => Slot.ofValue first :: ofFields rest
  termination_by fields => sizeOf fields
end

mutual
  def Slot.materialize : Slot → Option Value
    | .empty => none
    | .boolean value => some (.boolean value)
    | .number value => some (.number value)
    | .node kind variant fields => Value.node kind variant <$> materializeFields fields
    | .shared target => some (.reference target)
    | .boxed child => Value.boxed <$> Slot.materialize child
  termination_by part => sizeOf part

  def materializeFields : List Slot → Option (List Value)
    | [] => some []
    | first :: rest => do
      let value ← first.materialize
      let values ← materializeFields rest
      pure (value :: values)
  termination_by fields => sizeOf fields
end

mutual
  theorem Slot.materialize_ofValue (value : Value) : (Slot.ofValue value).materialize = some value := by
    cases value with
    | boolean value | number value | reference value => simp only [Slot.ofValue, Slot.materialize]
    | boxed child => simp only [Slot.ofValue, Slot.materialize, Slot.materialize_ofValue child, Functor.map, Option.map_some]
    | node kind variant fields => simp only [Slot.ofValue, Slot.materialize, materializeFields_ofFields fields, Functor.map, Option.map_some]
  termination_by sizeOf value

  theorem materializeFields_ofFields (fields : List Value) : materializeFields (ofFields fields) = some fields := by
    cases fields with
    | nil => simp only [ofFields, materializeFields]
    | cons first rest => simp only [ofFields, materializeFields, Slot.materialize_ofValue first,
        materializeFields_ofFields rest, bind, Option.bind, pure]
  termination_by sizeOf fields
end

mutual
  theorem Slot.eq_of_materialize (part : Slot) {value : Value} (h : part.materialize = some value) :
      part = Slot.ofValue value := by
    cases part with
    | empty => simp [Slot.materialize] at h
    | boolean b | number n | shared target =>
      simp only [Slot.materialize, Option.some.injEq] at h
      subst value
      simp only [Slot.ofValue]
    | boxed child =>
      cases hc : child.materialize with
      | none => simp [Slot.materialize, hc] at h
      | some childValue =>
        simp only [Slot.materialize, hc, Functor.map, Option.map_some, Option.some.injEq] at h
        subst value
        simpa only [Slot.ofValue] using congrArg Slot.boxed (child.eq_of_materialize hc)
    | node kind variant fields =>
      cases hf : materializeFields fields with
      | none => simp [Slot.materialize, hf] at h
      | some values =>
        simp only [Slot.materialize, hf, Functor.map, Option.map_some, Option.some.injEq] at h
        subst value
        simpa only [Slot.ofValue] using congrArg (Slot.node kind variant) (eq_of_materializeFields fields hf)
  termination_by sizeOf part

  theorem eq_of_materializeFields (fields : List Slot) {values : List Value}
      (h : materializeFields fields = some values) : fields = ofFields values := by
    cases fields with
    | nil =>
      simp only [materializeFields, Option.some.injEq] at h
      subst values
      simp only [ofFields]
    | cons first rest =>
      cases hf : first.materialize with
      | none => simp [materializeFields, hf] at h
      | some value =>
        cases hr : materializeFields rest with
        | none => simp [materializeFields, hf, hr] at h
        | some remaining =>
          simp only [materializeFields, hf, hr, bind, Option.bind, pure, Option.some.injEq] at h
          subst values
          rw [first.eq_of_materialize hf, eq_of_materializeFields rest hr]
          simp only [ofFields]
  termination_by sizeOf fields
end

/-- Logical destructor visits and released Box owners. A shared referent is
not traversed. Partially moved fields contribute no visits or owners. -/
structure DropWork where
  visits : Nat := 0
  boxes : Nat := 0
  deriving DecidableEq, Repr

def DropWork.plus (first second : DropWork) : DropWork :=
  ⟨first.visits + second.visits, first.boxes + second.boxes⟩

@[simp] theorem DropWork.zero_plus (work : DropWork) : ({} : DropWork).plus work = work := by
  cases work; simp [plus]

@[simp] theorem DropWork.plus_zero (work : DropWork) : work.plus {} = work := by
  cases work; simp [plus]

theorem DropWork.plus_assoc (a b c : DropWork) : (a.plus b).plus c = a.plus (b.plus c) := by
  cases a; cases b; cases c; simp [plus, Nat.add_assoc]

theorem DropWork.plus_comm (a b : DropWork) : a.plus b = b.plus a := by
  cases a; cases b; simp [plus, Nat.add_comm]

mutual
  def Slot.dropWork : Slot → DropWork
    | .empty => {}
    | .boolean _ | .number _ | .shared _ => ⟨1, 0⟩
    | .node _ _ fields => (⟨1, 0⟩ : DropWork).plus (dropFields fields)
    | .boxed child => (⟨1, 1⟩ : DropWork).plus child.dropWork
  termination_by part => sizeOf part

  def dropFields : List Slot → DropWork
    | [] => {}
    | first :: rest => first.dropWork.plus (dropFields rest)
  termination_by fields => sizeOf fields
end

end SubtreeProofs.Rust.LookupSource.Partial
