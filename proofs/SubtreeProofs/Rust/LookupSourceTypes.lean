module

public import SubtreeProofs.Rust.LookupHeapTyping

/-! Executable lifetime-erased type equality and independent constructor/
projection signatures. These rules use the existing heap `Shape` relation;
JSON declaration checking is a separate layer. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

mutual
  def same : Ty → Ty → Bool
    | .boolean, .boolean | .u32, .u32 => true
    | .adt first, .adt second => first == second
    | .shared first, .shared second | .owned first, .owned second => same first second
    | .tuple first, .tuple second => sameList first second
    | _, _ => false
  termination_by first _ => sizeOf first

  def sameList : List Ty → List Ty → Bool
    | [], [] => true
    | first :: rest, second :: tail => same first second && sameList rest tail
    | _, _ => false
  termination_by first _ => sizeOf first
end

mutual
  theorem same_eq {first second : Ty} (h : same first second = true) : first = second := by
    cases first <;> cases second <;> simp only [same, Bool.false_eq_true] at h
    all_goals first
      | rfl
      | exact congrArg Ty.adt (by simpa using h)
      | exact congrArg Ty.shared (same_eq h)
      | exact congrArg Ty.owned (same_eq h)
      | exact congrArg Ty.tuple (sameList_eq h)
  termination_by sizeOf first
  decreasing_by all_goals (subst_vars; simp_wf)

  theorem sameList_eq {first second : List Ty} (h : sameList first second = true) : first = second := by
    cases first with
    | nil => cases second with
      | nil => rfl
      | cons _ _ => simp [sameList] at h
    | cons head tail => cases second with
      | nil => simp [sameList] at h
      | cons other rest =>
        simp only [sameList] at h
        have hh := Bool.and_eq_true_iff.mp h
        rw [same_eq hh.1, sameList_eq hh.2]
  termination_by sizeOf first
  decreasing_by all_goals (subst_vars; simp_wf); all_goals omega
end

mutual
  theorem same_refl (ty : Ty) : same ty ty = true :=
    match ty with
    | .boolean | .u32 => by simp [same]
    | .adt kind => by simp [same]
    | .shared inner | .owned inner => by simpa only [same] using same_refl inner
    | .tuple types => by simpa only [same] using sameList_refl types
  termination_by sizeOf ty

  theorem sameList_refl (types : List Ty) : sameList types types = true :=
    match types with
    | [] => by simp [sameList]
    | first :: rest => by simp only [sameList, same_refl first, sameList_refl rest, Bool.and_true]
  termination_by sizeOf types
end

theorem same_iff (first second : Ty) : same first second = true ↔ first = second :=
  ⟨same_eq, by rintro rfl; exact same_refl first⟩

theorem sameList_iff (first second : List Ty) : sameList first second = true ↔ first = second :=
  ⟨sameList_eq, by rintro rfl; exact sameList_refl first⟩

def constructorFields : Kind → Nat → Ty → Option (List Ty)
  | .word, 0, .adt .word => some []
  | .word, 1, .adt .word => some [.owned (.adt .word), .owned (.adt .word)]
  | .table, 0, .adt .table => some []
  | .table, 1, .adt .table => some [.owned (.adt .entry), .owned (.adt .table)]
  | .entry, 0, .adt .entry => some [.adt .word, .adt .word, .adt .embedding]
  | .embedding, 0, .adt .embedding => some [.adt .word, .u32]
  | .optional, 0, .adt .optional => some []
  | .optional, 1, .adt .optional => some [.adt .embedding]
  | .tuple, 0, .tuple types => some types
  | _, _, _ => none

theorem constructorFields_sound {kind : Kind} {variant : Nat} {ty : Ty} {fields : List Ty}
    (h : constructorFields kind variant ty = some fields) : Shape kind variant fields ty := by
  unfold constructorFields at h
  split at h <;> cases h <;> constructor

theorem constructorFields_complete {kind : Kind} {variant : Nat} {ty : Ty} {fields : List Ty}
    (h : Shape kind variant fields ty) : constructorFields kind variant ty = some fields := by
  cases h <;> rfl

def deref : Ty → Option Ty
  | .shared inner | .owned inner => some inner
  | _ => none

def fieldType (ty : Ty) (variant : Option Nat) (index : Nat) : Option Ty := do
  match ty, variant with
  | .tuple types, none => types[index]?
  | .adt .entry, none => (← constructorFields .entry 0 ty)[index]?
  | .adt .embedding, none => (← constructorFields .embedding 0 ty)[index]?
  | .adt kind, some variant => (← constructorFields kind variant ty)[index]?
  | _, _ => none

def copyable : Ty → Bool
  | .boolean | .u32 | .shared _ => true
  | _ => false

def inputs : Function → List Ty
  | .copyWord => [.shared (.adt .word)]
  | .compare => [.shared (.adt .word), .shared (.adt .word)]
  | .copyResult => [.shared (.adt .embedding)]
  | .lookup => [.shared (.adt .table), .shared (.adt .word), .shared (.adt .word)]
  | .boxNew => []

def output : Function → Ty
  | .copyWord => .adt .word
  | .compare => .boolean
  | .copyResult => .adt .embedding
  | .lookup => .adt .optional
  | .boxNew => .tuple []

def callOutput (function : Function) (args : List Ty) : Option Ty :=
  if function = .boxNew then
    match args with
    | [inner] => some (.owned inner)
    | _ => none
  else if sameList args (inputs function) then some (output function) else none

end SubtreeProofs.Rust.LookupSource.SourceTypes
