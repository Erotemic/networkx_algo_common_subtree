module

public import SubtreeProofs.Rust.LookupRegionTypes

/-! Region-bearing shared-reference interpretation in retained heap worlds.
The common call lifetime is a semantic witness for immutable, non-escaping
helper borrows; it is not a physical clock interval or mutable-loan model. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Regions

abbrev Valuation := Region → Memory → Prop

def callLifetime (base : Memory) : Valuation := fun _ current => Extends base current

mutual
  inductive Value (base current : Memory) (valuation : Valuation) : Cell → Ty → Prop where
    | boolean (value : Bool) : Value base current valuation (.boolean value) .boolean
    | number {value : Nat} : value < 2 ^ 32 → Value base current valuation (.number value) .u32
    | adt {cell : Cell} {kind : Kind} : Borrow.Safe base current cell (.adt kind) → Value base current valuation cell (.adt kind)
    | tuple {cells : List Cell} {types : List Ty} : FieldsValue base current valuation cells types →
        Value base current valuation (.node .tuple 0 cells) (.tuple types)
    | owned {address : Nat} {cell : Cell} {ty : Ty} : current[address]? = some cell →
        Value base current valuation cell ty → Value base current valuation (.owned address) (.owned ty)
    | shared {pointer : Pointer} {cell : Cell} {region : Region} {inner : Ty} :
        Borrow.Loan base pointer (erase inner) → read current pointer = some cell → valuation region current →
        Value base current valuation cell inner → Value base current valuation (.shared pointer) (.shared region inner)

  inductive FieldsValue (base current : Memory) (valuation : Valuation) : List Cell → List Ty → Prop where
    | nil : FieldsValue base current valuation [] []
    | cons {cell : Cell} {ty : Ty} {cells : List Cell} {types : List Ty} :
        Value base current valuation cell ty → FieldsValue base current valuation cells types →
        FieldsValue base current valuation (cell :: cells) (ty :: types)
end

mutual
  theorem Value.erases {base current : Memory} {valuation : Valuation} {cell : Cell} {ty : Ty}
      (h : Value base current valuation cell ty) : Borrow.Safe base current cell (erase ty) :=
    match h with
    | .boolean value => by simpa only [erase] using Borrow.Safe.boolean (base := base) (current := current) value
    | .number hb => by simpa only [erase] using Borrow.Safe.number (base := base) (current := current) hb
    | .adt hsafe => by simpa only [erase] using hsafe
    | .tuple fields => by simpa only [erase] using Borrow.Safe.node (.tuple _) fields.erases
    | .owned hr child => by simpa only [erase] using Borrow.Safe.owned hr child.erases
    | .shared loan _ _ _ => by simpa only [erase] using Borrow.Safe.shared (current := current) loan

  theorem FieldsValue.erases {base current : Memory} {valuation : Valuation} {cells : List Cell} {types : List Ty}
      (h : FieldsValue base current valuation cells types) : Borrow.FieldsSafe base current cells (eraseList types) :=
    match h with
    | .nil => by simpa only [eraseList] using Borrow.FieldsSafe.nil (base := base) (current := current)
    | .cons first rest => by simpa only [eraseList] using Borrow.FieldsSafe.cons first.erases rest.erases
end

mutual
  theorem realize {base current : Memory} (he : Extends base current) (ty : Ty) {cell : Cell}
      (h : Borrow.Safe base current cell (erase ty)) : Value base current (callLifetime base) cell ty := by
    cases ty with
    | boolean =>
      simp only [erase] at h
      cases h with
      | boolean value => exact .boolean value
      | node shape _ => cases shape
    | u32 =>
      simp only [erase] at h
      cases h with
      | number hb => exact .number hb
      | node shape _ => cases shape
    | adt kind => exact .adt (by simpa only [erase] using h)
    | owned inner =>
      simp only [erase] at h
      cases h with
      | owned hr child => exact .owned hr (realize he inner child)
      | node shape _ => cases shape
    | tuple types => simp only [erase] at h; cases h with
      | node shape fields => cases shape with | tuple _ => exact .tuple (realizeFields he types fields)
    | shared region inner => simp only [erase] at h; cases h with
      | node shape _ => cases shape
      | shared loan =>
        obtain ⟨target, hr, ht⟩ := loan.valid
        exact .shared loan (read_extends he hr) he (realize he inner (Borrow.from_base he ht))
  termination_by sizeOf ty

  theorem realizeFields {base current : Memory} (he : Extends base current) (types : List Ty) {cells : List Cell}
      (h : Borrow.FieldsSafe base current cells (eraseList types)) : FieldsValue base current (callLifetime base) cells types := by
    cases types with
    | nil => simp only [eraseList] at h; cases h; exact .nil
    | cons first rest => simp only [eraseList] at h; cases h with
      | cons hf ht => exact .cons (realize he first hf) (realizeFields he rest ht)
  termination_by sizeOf types
end

theorem erasure_iff {base current : Memory} (he : Extends base current) (ty : Ty) (cell : Cell) :
    Value base current (callLifetime base) cell ty ↔ Borrow.Safe base current cell (erase ty) :=
  ⟨Value.erases, realize he ty⟩

theorem rename_iff {base current : Memory} (he : Extends base current) (mapping : Region → Region) (ty : Ty) (cell : Cell) :
    Value base current (callLifetime base) cell (rename mapping ty) ↔ Value base current (callLifetime base) cell ty := by
  rw [erasure_iff he, erasure_iff he, erase_rename]

def ScopedValue (base current : Memory) (scope : Scope) (valuation : Valuation) (cell : Cell) (ty : Ty) : Prop :=
  Scoped scope ty ∧ Value base current valuation cell ty

theorem scoped_erasure_iff {base current : Memory} {scope : Scope} (he : Extends base current)
    {ty : Ty} (hw : Scoped scope ty) (cell : Cell) :
    ScopedValue base current scope (callLifetime base) cell ty ↔ Borrow.Safe base current cell (erase ty) :=
  ⟨fun h => h.2.erases, fun h => ⟨hw, realize he ty h⟩⟩

theorem instantiate_value {base current : Memory} {arguments : List Region} {freeCount bodyCount : Nat}
    {ty : Ty} {cell : Cell} (he : Extends base current) (hlen : arguments.length = freeCount)
    (hargs : ∀ region ∈ arguments, Bound (.body bodyCount) region) (hw : Scoped (.signature freeCount) ty)
    (h : Borrow.Safe base current cell (erase ty)) :
    ScopedValue base current (.body bodyCount) (callLifetime base) cell (rename (substitute arguments) ty) :=
  ⟨instantiate_scoped hlen hargs hw, realize he _ (by simpa only [erase_rename] using h)⟩

theorem Checked.realize {base current : Memory} {scope : Scope} {expected : Heap.Ty}
    (annotation : Checked scope expected) (he : Extends base current) {cell : Cell}
    (h : Borrow.Safe base current cell expected) : ScopedValue base current scope (callLifetime base) cell annotation.type :=
  ⟨annotation.wf, Regions.realize he annotation.type (by simpa only [annotation.erases] using h)⟩

theorem eraseList_get (types : List Ty) (index : Nat) : (eraseList types)[index]? = (types[index]?).map erase := by
  induction index generalizing types with
  | zero => cases types <;> simp [eraseList]
  | succ index ih => cases types with
    | nil => simp [eraseList]
    | cons first rest => simpa only [eraseList, List.getElem?_cons_succ] using ih rest

theorem scoped_get {scope : Scope} {types : List Ty} (h : FieldsScoped scope types) (index : Nat) {ty : Ty}
    (ht : types[index]? = some ty) : Scoped scope ty := by
  induction index generalizing types with
  | zero => cases h with
    | nil => cases ht
    | cons first rest => cases ht; exact first
  | succ index ih => cases h with
    | nil => cases ht
    | cons first rest => exact ih rest ht

def EnvValue (base current : Memory) (scope : Scope) (valuation : Valuation) (types : List Ty) (env : Locals) : Prop :=
  ∀ slot cell, env slot = some cell → ∃ ty, types[slot]? = some ty ∧ ScopedValue base current scope valuation cell ty

theorem EnvSafe.regional {base current : Memory} {scope : Scope} {locals : List Heap.Ty} {env : Locals}
    (annotations : CheckedFields scope locals) (he : Extends base current) (h : Borrow.EnvSafe base current locals env) :
    EnvValue base current scope (callLifetime base) annotations.types env := by
  intro slot cell hc
  obtain ⟨expected, ht, hv⟩ := h slot cell hc
  have hl : (annotations.types[slot]?).map erase = some expected := by
    rw [← eraseList_get, annotations.erases]
    exact ht
  cases hs : annotations.types[slot]? with
  | none => simp [hs] at hl
  | some ty =>
    simp only [hs, Option.map_some, Option.some.injEq] at hl
    refine ⟨ty, rfl, scoped_get annotations.wf slot hs, ?_⟩
    exact realize he ty (by simpa only [hl] using hv)

end SubtreeProofs.Rust.LookupSource.Heap.Regions
