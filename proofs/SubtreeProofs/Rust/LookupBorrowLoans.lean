module

public import SubtreeProofs.Rust.LookupTypePrimitives

/-! Typed shared loans into a retained caller heap. Loan validity is backed
by an actual earlier read, so it survives every immutable heap extension.
Regions and mutable/freeing behavior are separate source obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

structure Loan (base : Memory) (pointer : Pointer) (ty : Ty) : Prop where
  valid : ∃ cell, read base pointer = some cell ∧ Typed base cell ty

theorem Loan.stable {base current : Memory} {pointer : Pointer} {ty : Ty}
    (h : Loan base pointer ty) (he : Extends base current) :
    ∃ cell, read current pointer = some cell ∧ Typed current cell ty := by
  obtain ⟨cell, hr, ht⟩ := h.valid
  exact ⟨cell, read_extends he hr, SourceTypes.typed_mono he ht⟩

theorem Loan.root_bound {base : Memory} {pointer : Pointer} {ty : Ty} (h : Loan base pointer ty) :
    pointer.root < base.length := by
  obtain ⟨cell, hr, _⟩ := h.valid
  unfold read at hr
  cases hp : base[pointer.root]? with
  | none => simp [hp] at hr
  | some value => exact List.getElem?_eq_some_iff.mp hp |>.choose

mutual
  inductive Safe (base current : Memory) : Cell → Ty → Prop where
    | boolean (value : Bool) : Safe base current (.boolean value) .boolean
    | number {value : Nat} : value < 2 ^ 32 → Safe base current (.number value) .u32
    | node {kind : Kind} {variant : Nat} {cells : List Cell} {types : List Ty} {ty : Ty} :
        Shape kind variant types ty → FieldsSafe base current cells types →
        Safe base current (.node kind variant cells) ty
    | shared {pointer : Pointer} {ty : Ty} : Loan base pointer ty → Safe base current (.shared pointer) (.shared ty)
    | owned {address : Nat} {cell : Cell} {ty : Ty} :
        current[address]? = some cell → Safe base current cell ty → Safe base current (.owned address) (.owned ty)

  inductive FieldsSafe (base current : Memory) : List Cell → List Ty → Prop where
    | nil : FieldsSafe base current [] []
    | cons {cell : Cell} {ty : Ty} {cells : List Cell} {types : List Ty} :
        Safe base current cell ty → FieldsSafe base current cells types →
        FieldsSafe base current (cell :: cells) (ty :: types)
end

mutual
  theorem Safe.typed {base current : Memory} (he : Extends base current) {cell : Cell} {ty : Ty}
      (h : Safe base current cell ty) : Typed current cell ty :=
    match h with
    | .boolean value => .boolean value
    | .number hb => .number hb
    | .node shape fields => .node shape (fields.typed he)
    | .shared hl => by obtain ⟨cell, hr, ht⟩ := hl.stable he; exact .shared hr ht
    | .owned hr child => .owned hr (child.typed he)

  theorem FieldsSafe.typed {base current : Memory} (he : Extends base current)
      {cells : List Cell} {types : List Ty} (h : FieldsSafe base current cells types) : FieldsTyped current cells types :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.typed he) (rest.typed he)
end

mutual
  theorem Safe.mono {base before after : Memory} (he : Extends before after) {cell : Cell} {ty : Ty}
      (h : Safe base before cell ty) : Safe base after cell ty :=
    match h with
    | .boolean value => .boolean value
    | .number hb => .number hb
    | .node shape fields => .node shape (fields.mono he)
    | .shared hl => .shared hl
    | .owned hr child => .owned (he _ _ hr) (child.mono he)

  theorem FieldsSafe.mono {base before after : Memory} (he : Extends before after)
      {cells : List Cell} {types : List Ty} (h : FieldsSafe base before cells types) : FieldsSafe base after cells types :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (first.mono he) (rest.mono he)
end

mutual
  theorem from_base {base current : Memory} (he : Extends base current) {cell : Cell} {ty : Ty}
      (h : Typed base cell ty) : Safe base current cell ty :=
    match h with
    | .boolean value => .boolean value
    | .number hb => .number hb
    | .node shape fields => .node shape (fields_from_base he fields)
    | .shared hr ht => .shared ⟨⟨_, hr, ht⟩⟩
    | .owned hr child => .owned (he _ _ hr) (from_base he child)

  theorem fields_from_base {base current : Memory} (he : Extends base current)
      {cells : List Cell} {types : List Ty} (h : FieldsTyped base cells types) : FieldsSafe base current cells types :=
    match h with
    | .nil => .nil
    | .cons first rest => .cons (from_base he first) (fields_from_base he rest)
end

def EnvSafe (base current : Memory) (locals : List Ty) (env : Locals) : Prop :=
  ∀ slot cell, env slot = some cell → ∃ ty, locals[slot]? = some ty ∧ Safe base current cell ty

theorem EnvSafe.get {base current : Memory} {locals : List Ty} {env : Locals}
    (h : EnvSafe base current locals env) {slot : Nat} {cell : Cell} {ty : Ty}
    (hc : env slot = some cell) (ht : locals[slot]? = some ty) : Safe base current cell ty := by
  obtain ⟨actual, ha, hv⟩ := h slot cell hc
  rw [ht] at ha
  cases ha
  exact hv

theorem EnvSafe.clear {base current : Memory} {locals : List Ty} {env : Locals}
    (h : EnvSafe base current locals env) (slot : Nat) : EnvSafe base current locals (env.set slot none) := by
  intro index cell hc
  by_cases hi : index = slot
  · simp [Locals.set, hi] at hc
  · exact h index cell (by simpa only [Locals.set, hi, ite_false] using hc)

theorem EnvSafe.store {base current : Memory} {locals : List Ty} {env : Locals}
    (h : EnvSafe base current locals env) {slot : Nat} {cell : Cell} {ty : Ty}
    (ht : locals[slot]? = some ty) (hv : Safe base current cell ty) : EnvSafe base current locals (env.set slot (some cell)) := by
  intro index value hc
  by_cases hi : index = slot
  · subst index
    simp only [Locals.set, ite_true, Option.some.injEq] at hc
    subst value
    exact ⟨ty, ht, hv⟩
  · exact h index value (by simpa only [Locals.set, hi, ite_false] using hc)

theorem EnvSafe.mono {base before after : Memory} (he : Extends before after)
    {locals : List Ty} {env : Locals} (h : EnvSafe base before locals env) : EnvSafe base after locals env := by
  intro slot cell hc
  obtain ⟨ty, ht, hv⟩ := h slot cell hc
  exact ⟨ty, ht, hv.mono he⟩

def fromShared (locals : List Ty) : Place → Bool
  | .local _ => false
  | .field parent _ _ => fromShared locals parent
  | .deref parent =>
    match SourceTypes.inferPlace locals parent with
    | some (.shared _) => true
    | some (.owned _) => fromShared locals parent
    | _ => false

def rvalueRoutes (locals : List Ty) : RValue → Bool
  | .address place => fromShared locals place
  | _ => true

def actionRoutes {F : Type} (locals : List Ty) : Action F → Bool
  | .assign _ rhs => rvalueRoutes locals rhs
  | _ => true

def codeRoutes {F : Type} (locals : List Ty) : LookupSource.Code F → Bool
  | .done | .ret => true
  | .step instruction rest => actionRoutes locals instruction && codeRoutes locals rest
  | .branch _ _ _ yes no rest => codeRoutes locals yes && codeRoutes locals no && codeRoutes locals rest

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
