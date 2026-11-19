module

public import SubtreeProofs.Rust.LookupBorrowLoans

/-! Supported source region binders and region-bearing types. Body regions
are existential IDs in the pinned Charon AST, not statement offsets. Erasure
and well-scoped substitution are independent of the source JSON reader. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions

inductive Region where
  | free : Nat → Region
  | body : Nat → Region
  deriving DecidableEq, Repr

inductive Scope where
  | signature : Nat → Scope
  | body : Nat → Scope
  deriving DecidableEq, Repr

def Bound : Scope → Region → Prop
  | .signature count, .free index => index < count
  | .body count, .body index => index < count
  | _, _ => False

inductive Ty where
  | boolean
  | u32
  | adt : Kind → Ty
  | owned : Ty → Ty
  | option : Ty → Ty
  | tuple : List Ty → Ty
  | shared : Region → Ty → Ty

mutual
  def erase : Ty → Heap.Ty
    | .boolean => .boolean
    | .u32 => .u32
    | .adt kind => .adt kind
    | .owned inner => .owned (erase inner)
    | .option inner => .option (erase inner)
    | .tuple types => .tuple (eraseList types)
    | .shared _ inner => .shared (erase inner)
  termination_by ty => sizeOf ty

  def eraseList : List Ty → List Heap.Ty
    | [] => []
    | first :: rest => erase first :: eraseList rest
  termination_by types => sizeOf types
end

mutual
  inductive Scoped (scope : Scope) : Ty → Prop where
    | boolean : Scoped scope .boolean
    | u32 : Scoped scope .u32
    | adt (kind : Kind) : Scoped scope (.adt kind)
    | owned {inner : Ty} : Scoped scope inner → Scoped scope (.owned inner)
    | option {inner : Ty} : Scoped scope inner → Scoped scope (.option inner)
    | tuple {types : List Ty} : FieldsScoped scope types → Scoped scope (.tuple types)
    | shared {region : Region} {inner : Ty} : Bound scope region → Scoped scope inner → Scoped scope (.shared region inner)

  inductive FieldsScoped (scope : Scope) : List Ty → Prop where
    | nil : FieldsScoped scope []
    | cons {first : Ty} {rest : List Ty} : Scoped scope first → FieldsScoped scope rest → FieldsScoped scope (first :: rest)
end

mutual
  def rename (mapping : Region → Region) : Ty → Ty
    | .boolean => .boolean
    | .u32 => .u32
    | .adt kind => .adt kind
    | .owned inner => .owned (rename mapping inner)
    | .option inner => .option (rename mapping inner)
    | .tuple types => .tuple (renameList mapping types)
    | .shared region inner => .shared (mapping region) (rename mapping inner)
  termination_by ty => sizeOf ty

  def renameList (mapping : Region → Region) : List Ty → List Ty
    | [] => []
    | first :: rest => rename mapping first :: renameList mapping rest
  termination_by types => sizeOf types
end

mutual
  theorem erase_rename (mapping : Region → Region) (ty : Ty) : erase (rename mapping ty) = erase ty := by
    cases ty with
    | boolean | u32 | adt _ => simp only [rename, erase]
    | owned inner => simpa only [rename, erase] using congrArg Heap.Ty.owned (erase_rename mapping inner)
    | option inner => simpa only [rename, erase] using congrArg Heap.Ty.option (erase_rename mapping inner)
    | tuple types => simpa only [rename, erase] using congrArg Heap.Ty.tuple (eraseList_rename mapping types)
    | shared region inner => simpa only [rename, erase] using congrArg Heap.Ty.shared (erase_rename mapping inner)
  termination_by sizeOf ty

  theorem eraseList_rename (mapping : Region → Region) (types : List Ty) :
      eraseList (renameList mapping types) = eraseList types := by
    cases types with
    | nil => simp only [renameList, eraseList]
    | cons first rest => simp only [renameList, eraseList, erase_rename mapping first, eraseList_rename mapping rest]
  termination_by sizeOf types
end

mutual
  theorem Scoped.rename {before after : Scope} {mapping : Region → Region}
      (hm : ∀ region, Bound before region → Bound after (mapping region)) {ty : Ty} (h : Scoped before ty) :
      Scoped after (Regions.rename mapping ty) :=
    match h with
    | .boolean => by simpa only [Regions.rename] using Scoped.boolean (scope := after)
    | .u32 => by simpa only [Regions.rename] using Scoped.u32 (scope := after)
    | .adt kind => by simpa only [Regions.rename] using Scoped.adt (scope := after) kind
    | .owned inner => by simpa only [Regions.rename] using Scoped.owned (inner.rename hm)
    | .option inner => by simpa only [Regions.rename] using Scoped.option (inner.rename hm)
    | .tuple fields => by simpa only [Regions.rename] using Scoped.tuple (fields.rename hm)
    | .shared hb inner => by simpa only [Regions.rename] using Scoped.shared (hm _ hb) (inner.rename hm)

  theorem FieldsScoped.rename {before after : Scope} {mapping : Region → Region}
      (hm : ∀ region, Bound before region → Bound after (mapping region)) {types : List Ty}
      (h : FieldsScoped before types) : FieldsScoped after (renameList mapping types) :=
    match h with
    | .nil => by simpa only [renameList] using FieldsScoped.nil (scope := after)
    | .cons first rest => by simpa only [renameList] using FieldsScoped.cons (first.rename hm) (rest.rename hm)
end

def substitute (arguments : List Region) : Region → Region
  | .free index => arguments[index]?.getD (.free index)
  | .body index => .body index

theorem substitute_bound {arguments : List Region} {freeCount bodyCount : Nat}
    (hlen : arguments.length = freeCount) (hargs : ∀ region ∈ arguments, Bound (.body bodyCount) region)
    (region : Region) (hb : Bound (.signature freeCount) region) :
    Bound (.body bodyCount) (substitute arguments region) := by
  cases region with
  | body index => cases hb
  | free index =>
    have hi : index < arguments.length := by simpa only [Bound, hlen] using hb
    have he : arguments[index]? = some arguments[index] := List.getElem?_eq_getElem hi
    simpa only [substitute, he, Option.getD_some] using hargs _ (List.getElem_mem hi)

theorem instantiate_scoped {arguments : List Region} {freeCount bodyCount : Nat} {ty : Ty}
    (hlen : arguments.length = freeCount) (hargs : ∀ region ∈ arguments, Bound (.body bodyCount) region)
    (h : Scoped (.signature freeCount) ty) : Scoped (.body bodyCount) (rename (substitute arguments) ty) :=
  h.rename (substitute_bound hlen hargs)

structure Checked (scope : Scope) (expected : Heap.Ty) where
  type : Ty
  erases : erase type = expected
  wf : Scoped scope type

structure CheckedFields (scope : Scope) (expected : List Heap.Ty) where
  types : List Ty
  erases : eraseList types = expected
  wf : FieldsScoped scope types

end SubtreeProofs.Rust.LookupSource.Heap.Regions
