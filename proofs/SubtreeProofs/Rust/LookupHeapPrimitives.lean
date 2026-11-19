module

public import SubtreeProofs.Rust.LookupHeapMemory

/-! Concrete local reads/moves and shared heap borrows for the lookup fragment.
Borrowing a local stack address is rejected; source places must cross a pointer
dereference. This is checked separately for the actual lookup program. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

def locate (memory : Memory) (env : Locals) : Place → Option (Cell × Option Pointer)
  | .local slot => do some (← env slot, none)
  | .deref place => do
    let (value, _) ← locate memory env place
    match value with
    | .shared pointer => some (← read memory pointer, some pointer)
    | .owned address => some (← memory[address]?, some ⟨address, []⟩)
    | _ => none
  | .field place variant index => do
    let (value, address) ← locate memory env place
    match value with
    | .node _ actual values =>
      if variant.all (· = actual) then
        some (← values[index]?, address.map (·.field index))
      else none
    | _ => none

def heapBorrow : Place → Bool
  | .local _ => false
  | .deref _ => true
  | .field parent _ _ => heapBorrow parent

def borrow (memory : Memory) (env : Locals) (place : Place) : Option Cell := do
  let (_, address) ← locate memory env place
  return .shared (← address)

def operand (memory : Memory) (env : Locals) : Operand → Option (Cell × Locals)
  | .move slot => do some (← env slot, env.set slot none)
  | .boolean value => some (.boolean value, env)
  | .copy place => do
    let (value, _) ← locate memory env place
    match value with
    | .boolean _ | .number _ | .shared _ => some (value, env)
    | _ => none

def operands (memory : Memory) : List Operand → Locals → Option (List Cell × Locals)
  | [], env => some ([], env)
  | first :: rest, env => do
    let (value, env) ← operand memory env first
    let (values, env) ← operands memory rest env
    some (value :: values, env)

def rvalue (memory : Memory) (env : Locals) : RValue → Option (Cell × Locals)
  | .use value => operand memory env value
  | .address place => do some (← borrow memory env place, env)
  | .aggregate kind variant args => do
    let (values, env) ← operands memory args env
    some (.node kind variant values, env)

def heapBorrows : RValue → Bool
  | .address place => heapBorrow place
  | _ => true

theorem option_rep_some {memory : Memory} {cell : Option Cell} {value : Value}
    (h : Option.Rel (Represents memory) cell (some value)) :
    ∃ concrete, cell = some concrete ∧ Represents memory concrete value := by
  cases h with | some hr => exact ⟨_, rfl, hr⟩

theorem EnvRep.get {memory : Memory} {concrete : Locals} {abstract : Env}
    (h : EnvRep memory concrete abstract) {slot : Nat} {value : Value}
    (hr : abstract slot = some value) :
    ∃ cell, concrete slot = some cell ∧ Represents memory cell value := by
  have hx := h slot
  rw [hr] at hx
  exact option_rep_some hx

theorem locate_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (place : Place) {value : Value}
    (hr : readPlace abstract place = some value) :
    ∃ cell address, locate memory concrete place = some (cell, address) ∧
      Represents memory cell value ∧
      ∀ pointer, address = some pointer → read memory pointer = some cell := by
  induction place generalizing value with
  | «local» slot =>
    obtain ⟨cell, hc, hv⟩ := he.get hr
    exact ⟨cell, none, by simp [locate, hc], hv, by simp⟩
  | deref place ih =>
    simp only [readPlace] at hr
    cases hs : readPlace abstract place with
    | none => simp [hs] at hr
    | some parent =>
      simp only [hs, bind, Option.bind] at hr
      obtain ⟨cell, address, hl, hv, _⟩ := ih hs
      cases parent <;> simp only [Option.some.injEq] at hr
      all_goals try contradiction
      case reference v =>
        cases hr
        cases hv with
        | @shared pointer child _ hp hv =>
          exact ⟨child, some pointer, by simp [locate, hl, hp], hv,
            by intro p h; cases h; exact hp⟩
      case boxed v =>
        cases hr
        cases hv with
        | @owned pointer child _ hp hv =>
          exact ⟨child, some ⟨pointer, []⟩, by simp [locate, hl, hp], hv,
            by intro p h; cases h; simpa [read, fields] using hp⟩
  | field place variant index ih =>
    simp only [readPlace] at hr
    cases hs : readPlace abstract place with
    | none => simp [hs] at hr
    | some parent =>
      simp only [hs, bind, Option.bind] at hr
      obtain ⟨cell, address, hl, hv, hp⟩ := ih hs
      cases parent <;> try contradiction
      rename_i kind actual values
      cases hv with
      | node hv =>
        dsimp only at hr
        split at hr
        next hguard =>
          obtain ⟨result, hg, hv'⟩ := option_rep_some (by simpa only [hr] using hv.get index)
          refine ⟨result, address.map (·.field index), ?_, hv', ?_⟩
          · simp [locate, hl, hguard, hg]
          · intro pointer ha
            cases address with
            | none => simp at ha
            | some address =>
              simp only [Option.map_some, Option.some.injEq] at ha
              subst pointer
              rw [read_field (hp address rfl)]
              exact hg
        next => contradiction

theorem locate_has_address {memory : Memory} {env : Locals} (place : Place)
    (hb : heapBorrow place = true) {cell : Cell} {address : Option Pointer}
    (hr : locate memory env place = some (cell, address)) : ∃ pointer, address = some pointer := by
  induction place generalizing cell address with
  | «local» slot => cases hb
  | deref place ih =>
    simp only [locate] at hr
    cases hp : locate memory env place with
    | none => simp [hp] at hr
    | some pair =>
      rcases pair with ⟨parent, loc⟩
      cases parent <;> simp only [hp, bind, Option.bind] at hr <;> try contradiction
      all_goals
        split at hr <;> try contradiction
        cases hr
        exact ⟨_, rfl⟩
  | field place variant index ih =>
    simp only [locate] at hr
    cases hp : locate memory env place with
    | none => simp [hp] at hr
    | some pair =>
      rcases pair with ⟨parent, loc⟩
      obtain ⟨pointer, rfl⟩ := ih hb hp
      cases parent <;> simp only [hp, bind, Option.bind] at hr <;> try contradiction
      split at hr <;> try contradiction
      split at hr <;> try contradiction
      cases hr
      exact ⟨_, rfl⟩

theorem borrow_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (place : Place) (hb : heapBorrow place = true)
    {value : Value} (hr : readPlace abstract place = some value) :
    ∃ cell, borrow memory concrete place = some cell ∧ Represents memory cell (.reference value) := by
  obtain ⟨cell, address, hl, hv, hp⟩ := locate_spec he place hr
  obtain ⟨pointer, rfl⟩ := locate_has_address place hb hl
  exact ⟨.shared pointer, by simp [borrow, hl], .shared (hp pointer rfl) hv⟩

theorem operand_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (op : Operand) {value : Value} {next : Env}
    (hr : evalOperand abstract op = some (value, next)) :
    ∃ cell state, operand memory concrete op = some (cell, state) ∧
      Represents memory cell value ∧ EnvRep memory state next := by
  cases op with
  | move slot =>
    simp only [evalOperand] at hr
    cases hs : abstract slot with
    | none => simp [hs] at hr
    | some v =>
      simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨cell, hc, hv⟩ := he.get hs
      exact ⟨cell, concrete.set slot none, by simp [operand, hc], hv, he.set slot .none⟩
  | boolean b =>
    cases hr
    exact ⟨.boolean b, concrete, rfl, .boolean b, he⟩
  | copy place =>
    simp only [evalOperand] at hr
    cases hs : readPlace abstract place with
    | none => simp [hs] at hr
    | some parent =>
      obtain ⟨cell, address, hl, hv, _⟩ := locate_spec he place hs
      simp only [hs, bind, Option.bind] at hr
      cases parent <;> try contradiction
      all_goals
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        refine ⟨cell, concrete, ?_, hv, he⟩
        cases hv; simp [operand, hl]

theorem operands_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (args : List Operand) {values : List Value} {next : Env}
    (hr : evalOperands args abstract = some (values, next)) :
    ∃ cells state, operands memory args concrete = some (cells, state) ∧
      RepresentsFields memory cells values ∧ EnvRep memory state next := by
  induction args generalizing concrete abstract values next with
  | nil =>
    cases hr
    exact ⟨[], concrete, rfl, .nil, he⟩
  | cons first rest ih =>
    simp only [evalOperands] at hr
    cases hf : evalOperand abstract first with
    | none => simp [hf] at hr
    | some pair =>
      rcases pair with ⟨value, middle⟩
      cases hs : evalOperands rest middle with
      | none => simp [hf, hs] at hr
      | some pair =>
        rcases pair with ⟨vs, final⟩
        simp only [hf, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨cell, state, hc, hv, he'⟩ := operand_spec he first hf
        obtain ⟨cells, last, hcs, hvs, he''⟩ := ih he' hs
        exact ⟨cell :: cells, last, by simp [operands, hc, hcs], .cons hv hvs, he''⟩

theorem rvalue_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (rhs : RValue) (hb : heapBorrows rhs = true)
    {value : Value} {next : Env} (hr : evalRValue abstract rhs = some (value, next)) :
    ∃ cell state, rvalue memory concrete rhs = some (cell, state) ∧
      Represents memory cell value ∧ EnvRep memory state next := by
  cases rhs with
  | use op => exact operand_spec he op hr
  | address place =>
    simp only [evalRValue] at hr
    cases hs : readPlace abstract place with
    | none => simp [hs] at hr
    | some v =>
      simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨cell, hc, hv⟩ := borrow_spec he place hb hs
      exact ⟨cell, concrete, by simp [rvalue, hc], hv, he⟩
  | aggregate kind variant args =>
    simp only [evalRValue] at hr
    cases hs : evalOperands args abstract with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨vs, final⟩
      simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨cells, state, hc, hv, he'⟩ := operands_spec he args hs
      exact ⟨.node kind variant cells, state, by simp [rvalue, hc], .node hv, he'⟩

def scrutinee (memory : Memory) (env : Locals) : Scrutinee → Option (Key × Locals)
  | .value op => do
    let (value, env) ← operand memory env op
    match value with
    | .boolean b => some (.boolean b, env)
    | _ => none
  | .discriminant place => do
    let (value, _) ← locate memory env place
    match value with
    | .node kind variant _ => some (.variant kind variant, env)
    | _ => none

theorem scrutinee_spec {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (scrut : Scrutinee) {key : Key} {next : Env}
    (hr : evalScrutinee abstract scrut = some (key, next)) :
    ∃ state, scrutinee memory concrete scrut = some (key, state) ∧ EnvRep memory state next := by
  cases scrut with
  | value op =>
    simp only [evalScrutinee] at hr
    cases hs : evalOperand abstract op with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨value, final⟩
      obtain ⟨cell, state, hc, hv, he'⟩ := operand_spec he op hs
      simp only [hs, bind, Option.bind] at hr
      cases value <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      cases hv
      exact ⟨state, by simp [scrutinee, hc], he'⟩
  | discriminant place =>
    simp only [evalScrutinee] at hr
    cases hs : readPlace abstract place with
    | none => simp [hs] at hr
    | some parent =>
      obtain ⟨cell, address, hl, hv, _⟩ := locate_spec he place hs
      simp only [hs, bind, Option.bind] at hr
      cases parent <;> try contradiction
      simp only [Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      cases hv
      exact ⟨concrete, by simp [scrutinee, hl], he⟩

end SubtreeProofs.Rust.LookupSource.Heap
