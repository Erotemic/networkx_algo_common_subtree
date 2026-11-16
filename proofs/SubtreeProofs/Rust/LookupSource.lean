module

public import SubtreeProofs.Rust.LookupEvents

/-!
# Read-only LLBC fragment for the source-cost lookup pilot

This operational model is deliberately restricted to the four lookup functions.
Every represented statement and operand access is charged; a nontrivial call
delegates both value and cost to its callee. Moves invalidate their slot.
Conditional drops succeed only for already moved locals: live owned destruction
is unsupported, not free. Shared references are immutable value snapshots, not
heap addresses. Allocation charges count Box creation operations, not allocator
time or memory bytes. The Python reifier and its relation to LLBC remain trusted;
heapful Rust execution, field typing, aliasing/lifetimes, unwinding and stack
exhaustion are not verified by this model. A source digest and a compiled source
mutation provide provenance/regression evidence, not a proof of translation.
-/

@[expose] public section

register_simp_attr lookup_source_simps

namespace SubtreeProofs.Rust.LookupSource

inductive Kind where
  | word | table | entry | embedding | optional | tuple
  deriving DecidableEq, Repr

inductive Value where
  | boolean : Bool → Value
  | number : Nat → Value
  | node : Kind → Nat → List Value → Value
  | reference : Value → Value
  | boxed : Value → Value

inductive Key where
  | boolean : Bool → Key
  | variant : Kind → Nat → Key
  deriving DecidableEq, Repr

inductive Function where
  | copyWord | compare | copyResult | lookup | boxNew
  deriving DecidableEq, Repr

inductive Place where
  | local : Nat → Place
  | deref : Place → Place
  | field : Place → Option Nat → Nat → Place

abbrev Env := Nat → Option Value

def Env.set (env : Env) (slot : Nat) (value : Option Value) : Env :=
  fun index => if index = slot then value else env index

def Place.weight : Place → Nat
  | .local _ => 1
  | .deref place => place.weight + 1
  | .field place _ _ => place.weight + 1

def readPlace (env : Env) : Place → Option Value
  | .local slot => env slot
  | .deref place => do
    match ← readPlace env place with
    | .reference value | .boxed value => some value
    | _ => none
  | .field place variant field => do
    match ← readPlace env place with
    | .node _ actual fields =>
      if variant.all (· = actual) then fields[field]? else none
    | _ => none

inductive Operand where
  | move : Nat → Operand
  | copy : Place → Operand
  | boolean : Bool → Operand

def Operand.weight : Operand → Nat
  | .move _ => 1
  | .copy place => place.weight
  | .boolean _ => 1

def evalOperand (env : Env) : Operand → Option (Value × Env)
  | .move slot => do
    let value ← env slot
    some (value, env.set slot none)
  | .copy place => do
    let value ← readPlace env place
    match value with
    | .boolean _ | .number _ | .reference _ => some (value, env)
    | _ => none
  | .boolean value => some (.boolean value, env)

def evalOperands : List Operand → Env → Option (List Value × Env)
  | [], env => some ([], env)
  | operand :: rest, env => do
    let (value, env) ← evalOperand env operand
    let (values, env) ← evalOperands rest env
    some (value :: values, env)

inductive RValue where
  | use : Operand → RValue
  | address : Place → RValue
  | aggregate : Kind → Nat → List Operand → RValue

def RValue.weight : RValue → Nat
  | .use operand => operand.weight
  | .address place => place.weight + 1
  | .aggregate _ _ operands => 1 + (operands.map Operand.weight).sum

def evalRValue (env : Env) : RValue → Option (Value × Env)
  | .use operand => evalOperand env operand
  | .address place => do
    let value ← readPlace env place
    some (.reference value, env)
  | .aggregate kind variant operands => do
    let (fields, env) ← evalOperands operands env
    some (.node kind variant fields, env)

inductive Scrutinee where
  | value : Operand → Scrutinee
  | discriminant : Place → Scrutinee

def Scrutinee.weight : Scrutinee → Nat
  | .value operand => operand.weight
  | .discriminant place => place.weight + 1

def evalScrutinee (env : Env) : Scrutinee → Option (Key × Env)
  | .value operand => do
    let (value, env) ← evalOperand env operand
    match value with
    | .boolean b => some (.boolean b, env)
    | _ => none
  | .discriminant place => do
    match ← readPlace env place with
    | .node kind variant _ => some (.variant kind variant, env)
    | _ => none

inductive Action where
  | scope : Nat → Action
  | assign : Nat → RValue → Action
  | call : Function → List Operand → Nat → Action
  | dropMoved : Nat → Action

def Action.weight : Action → Nat
  | .scope _ | .dropMoved _ => 1
  | .assign _ value => 1 + value.weight
  | .call _ args _ => 1 + (args.map Operand.weight).sum

structure Cost where
  steps : Nat := 0
  events : LookupEvents.Events := {}

def Cost.plus (first second : Cost) : Cost :=
  ⟨first.steps + second.steps, first.events.plus second.events⟩

abbrev Callees := Function → List Value → Option (Value × Cost)

def evalAction (call : Callees) (env : Env) (action : Action) : Option (Env × Cost) := do
  match action with
  | .scope slot => some (env.set slot none, ⟨action.weight, {}⟩)
  | .assign slot value =>
    let (value, env) ← evalRValue env value
    some (env.set slot (some value), ⟨action.weight, {}⟩)
  | .call function args slot =>
    let (values, env) ← evalOperands args env
    let (value, cost) ← call function values
    some (env.set slot (some value), (⟨action.weight, {}⟩ : Cost).plus cost)
  | .dropMoved slot =>
    match env slot with
    | none => some (env, ⟨action.weight, {}⟩)
    | some _ => none

/-- Switch arms can return early or resume the common continuation. The second
key is absent exactly when the source has a fallback branch. -/
inductive Code where
  | done
  | ret
  | step : Action → Code → Code
  | branch : Scrutinee → Key → Option Key → Code → Code → Code → Code

inductive Outcome where
  | next : Env → Outcome
  | returned : Value → Outcome

def selectBranch {α : Type} (actual key : Key) (other : Option Key)
    (yes no : Unit → Option α) : Option α :=
  if actual = key then yes () else if other.all (· = actual) then no () else none

/-- Each syntax node charges its own work. No call is evaluated inside a free
pure expression; a callee's complete cost is composed at the call occurrence. -/
def exec (call : Callees) : Code → Env → Option (Outcome × Cost)
  | .done, env => some (.next env, {})
  | .ret, env => do
    let result ← env 0
    some (.returned result, ⟨1, {}⟩)
  | .step action rest, env => do
    let (env, first) ← evalAction call env action
    let (result, second) ← exec call rest env
    some (result, first.plus second)
  | .branch scrutinee key other yes no rest, env => do
    let (actual, env) ← evalScrutinee env scrutinee
    let (result, first) ← selectBranch actual key other
      (fun _ => exec call yes env) (fun _ => exec call no env)
    let charged := (⟨1 + scrutinee.weight, {}⟩ : Cost).plus first
    match result with
    | .returned value => some (.returned value, charged)
    | .next env =>
      let (result, last) ← exec call rest env
      some (result, charged.plus last)

/-- Local syntax envelope. Both arms are included through their maximum;
callee execution is excluded here and charged by its own complete contract. -/
def Code.budget : Code → Nat
  | .done => 0
  | .ret => 1
  | .step action rest => action.weight + rest.budget
  | .branch scrutinee _ _ yes no rest =>
    1 + scrutinee.weight + max yes.budget no.budget + rest.budget

theorem Cost.units_plus (a b : Cost) :
    (a.plus b).events.units = a.events.units + b.events.units := by
  simp only [Cost.plus, LookupEvents.Events.plus, LookupEvents.Events.units]
  omega

theorem action_bound (call : Callees) (price : Nat)
    (hc : ∀ function args value cost, call function args = some (value, cost) →
      cost.steps ≤ price * cost.events.units)
    {env next : Env} {action : Action} {cost : Cost}
    (hr : evalAction call env action = some (next, cost)) :
    cost.steps ≤ action.weight + price * cost.events.units := by
  cases action with
  | scope slot =>
    simp only [evalAction, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr
    simp [LookupEvents.Events.units]
  | assign slot rhs =>
    simp only [evalAction] at hr
    cases he : evalRValue env rhs with
    | none => simp [he] at hr
    | some result =>
      rcases result with ⟨value, state⟩
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      simp [LookupEvents.Events.units]
  | dropMoved slot =>
    simp only [evalAction] at hr
    cases he : env slot with
    | some value => simp [he] at hr
    | none =>
      simp only [he, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      simp [LookupEvents.Events.units]
  | call function args slot =>
    simp only [evalAction] at hr
    cases he : evalOperands args env with
    | none => simp [he] at hr
    | some result =>
      rcases result with ⟨values, state⟩
      simp only [he, bind, Option.bind] at hr
      cases hf : call function values with
      | none => simp [hf] at hr
      | some result =>
        rcases result with ⟨value, inner⟩
        have hb := hc function values value inner hf
        try simp only [hf, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨_, rfl⟩ := hr
        simp only [Cost.plus, LookupEvents.Events.plus, LookupEvents.Events.units] at *
        simp only [Nat.zero_add] at *
        omega

/-- A successful execution pays for every local instruction and every nested
call. This is independent of the four functions' value specifications. -/
theorem exec_bound (call : Callees) (price : Nat)
    (hc : ∀ function args value cost, call function args = some (value, cost) →
      cost.steps ≤ price * cost.events.units)
    {code : Code} {env : Env} {outcome : Outcome} {cost : Cost}
    (hr : exec call code env = some (outcome, cost)) :
    cost.steps ≤ code.budget + price * cost.events.units := by
  induction code generalizing env outcome cost with
  | done =>
    simp only [exec, Option.some.injEq, Prod.mk.injEq] at hr
    obtain ⟨_, rfl⟩ := hr
    simp [Code.budget, LookupEvents.Events.units]
  | ret =>
    simp only [exec] at hr
    cases he : env 0 with
    | none => simp [he] at hr
    | some value =>
      simp only [he, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨_, rfl⟩ := hr
      simp [Code.budget, LookupEvents.Events.units]
  | step action rest ih =>
    simp only [exec] at hr
    cases ha : evalAction call env action with
    | none => simp [ha] at hr
    | some pair =>
      rcases pair with ⟨next, first⟩
      have hb := action_bound call price hc ha
      simp only [ha, bind, Option.bind] at hr
      cases he : exec call rest next with
      | none => simp [he] at hr
      | some pair =>
        rcases pair with ⟨result, last⟩
        have hl := ih he
        try simp only [he, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨_, rfl⟩ := hr
        simp only [Code.budget, Cost.units_plus, Nat.mul_add]
        change first.steps + last.steps ≤ _
        omega
  | branch scrutinee key other yes no rest ihYes ihNo ihRest =>
    simp only [exec] at hr
    cases hs : evalScrutinee env scrutinee with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨actual, state⟩
      simp only [hs, bind, Option.bind] at hr
      have arm_bound : ∀ result c,
          selectBranch actual key other (fun _ => exec call yes state)
            (fun _ => exec call no state) = some (result, c) →
          c.steps ≤ max yes.budget no.budget + price * c.events.units := by
        intro result c he
        unfold selectBranch at he
        split at he
        · have h := ihYes he
          have hm := Nat.le_max_left yes.budget no.budget
          omega
        · split at he
          · have h := ihNo he
            have hm := Nat.le_max_right yes.budget no.budget
            omega
          · cases he
      cases he : selectBranch actual key other (fun _ => exec call yes state)
          (fun _ => exec call no state) with
      | none => simp [he] at hr
      | some pair =>
        rcases pair with ⟨result, first⟩
        have hb := arm_bound result first he
        try simp only [he] at hr
        cases result with
        | returned value =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨_, rfl⟩ := hr
          simp only [Code.budget, Cost.plus, LookupEvents.Events.plus,
            LookupEvents.Events.units] at *
          simp only [Nat.zero_add] at *
          omega
        | next next =>
          cases ht : exec call rest next with
          | none => simp [ht] at hr
          | some pair =>
            rcases pair with ⟨result, last⟩
            have hl := ihRest ht
            simp only [ht, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨_, rfl⟩ := hr
            simp only [Code.budget, Cost.plus,
              LookupEvents.Events.plus, LookupEvents.Events.units, Nat.mul_add] at *
            omega

def initialEnv (args : List Value) : Env :=
  fun index => if index = 0 then none else args[index - 1]?

def entryEvents : Function → LookupEvents.Events
  | .copyWord => { copyNodes := 1 }
  | .compare => { compareNodes := 1 }
  | .copyResult => { resultCopies := 1 }
  | .lookup => { lookupNodes := 1 }
  | .boxNew => { allocations := 1 }

/-- Supply generated bodies explicitly. Fuel limits call nesting only; steps
are counted additively by exec, never inferred from fuel. -/
def run (body : Function → Code) : Nat → Callees
  | 0, _, _ => none
  | fuel + 1, function, args =>
    if function = .boxNew then
      match args with
      | [value] => some (.boxed value, ⟨1, entryEvents function⟩)
      | _ => none
    else do
      let (outcome, cost) ← exec (run body fuel) (body function) (initialEnv args)
      match outcome with
      | .next _ => none
      | .returned value =>
        some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)

theorem run_succ (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) :
    run body (fuel + 1) function args =
      (if function = .boxNew then
        match args with
        | [value] => some (.boxed value, ⟨1, entryEvents function⟩)
        | _ => none
      else do
        let (outcome, cost) ← exec (run body fuel) (body function) (initialEnv args)
        match outcome with
        | .next _ => none
        | .returned value =>
          some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)) := by rfl

theorem entry_units (function : Function) : (entryEvents function).units = 1 := by
  cases function <;> rfl

/-- Source-operation bound for every complete execution, without assuming
correct results, well-typed inputs, or the old packet-count theorem. -/
theorem run_bound (body : Function → Code) (price : Nat) (hp : 1 ≤ price)
    (hb : ∀ function, (body function).budget + 1 ≤ price)
    {fuel : Nat} {function : Function} {args : List Value} {value : Value} {cost : Cost}
    (hr : run body fuel function args = some (value, cost)) :
    cost.steps ≤ price * cost.events.units := by
  induction fuel generalizing function args value cost with
  | zero => simp [run] at hr
  | succ fuel ih =>
    by_cases hf : function = .boxNew
    ·
      subst function
      rw [run_succ] at hr
      simp only [↓reduceIte] at hr
      cases args with
      | nil => simp at hr
      | cons first rest =>
        cases rest with
        | cons _ _ => simp at hr
        | nil =>
          try simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨_, rfl⟩ := hr
          simpa only [entry_units, Nat.mul_one] using hp
    · rw [run_succ, ite_eq_right hf] at hr
      cases he : exec (run body fuel) (body function) (initialEnv args) with
      | none => simp [he] at hr
      | some pair =>
        rcases pair with ⟨outcome, inner⟩
        have hinner := exec_bound (run body fuel) price
          (fun _ _ _ _ h => ih h) he
        simp only [he, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned result =>
          try simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨_, rfl⟩ := hr
          have hbudget := hb function
          have hu := Cost.units_plus (⟨1, entryEvents function⟩ : Cost) inner
          simp only [entry_units] at hu
          rw [hu, Nat.mul_add, Nat.mul_one]
          change 1 + inner.steps ≤ _
          omega

def encodeWord : verified_ordered_core.BalancedWord → Value
  | .Empty => .node .word 0 []
  | .Pair head tail => .node .word 1 [.boxed (encodeWord head), .boxed (encodeWord tail)]

def encodeResult (result : verified_ordered_core.CommonEmbedding) : Value :=
  .node .embedding 0 [encodeWord result.word, .number result.edges.val]

def encodeTable : verified_ordered_core.MemoTable → Value
  | .Empty => .node .table 0 []
  | .Entry entry rest => .node .table 1 [
      .boxed (.node .entry 0 [encodeWord entry.left, encodeWord entry.right, encodeResult entry.result]),
      .boxed (encodeTable rest)]

def encodeOption : Option verified_ordered_core.CommonEmbedding → Value
  | none => .node .optional 0 []
  | some result => .node .optional 1 [encodeResult result]

end SubtreeProofs.Rust.LookupSource
