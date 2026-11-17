module

public import SubtreeProofs.Rust.LookupSource

/-! Checked control normalization for the pinned binary LLBC lookup fragment.
Source switches retain their original branch-index table and fallback; source
storage-live/dead markers remain distinct until lowering. The source executor
selects an index directly, independently of the normalized `Code` dispatcher.
Primitives share the existing snapshot operational model. This proves control
and cost preservation inside that model, not typed heap/Rust adequacy. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Control

deriving instance DecidableEq for Place
deriving instance DecidableEq for Operand
deriving instance DecidableEq for RValue
deriving instance DecidableEq for Scrutinee
deriving instance DecidableEq for LookupSource.Action
deriving instance DecidableEq for Code

inductive Action (F : Type := Function) where
  | storageLive : Nat → Action F
  | storageDead : Nat → Action F
  | assign : Nat → RValue → Action F
  | call : F → List Operand → Nat → Action F
  | dropConditional : Nat → Action F

def Action.lower {F : Type} : Action F → LookupSource.Action F
  | .storageLive slot | .storageDead slot => .scope slot
  | .assign slot rhs => .assign slot rhs
  | .call function args dest => .call function args dest
  | .dropConditional slot => .dropMoved slot

/-- The common primitive semantics is explicit. In particular a conditional
drop of a live owned value fails; it is not silently given zero destruction. -/
def Action.exec {F : Type} (call : CalleesFor F) (env : Env) (action : Action F) : Option (Env × Cost) :=
  evalAction call env action.lower

inductive Tree (A : Type) where
  | done : Tree A
  | ret : Tree A
  | step : A → Tree A → Tree A
  | switch : Scrutinee → List (Key × Nat) → Option Nat → Tree A → Tree A → Tree A → Tree A
  deriving DecidableEq

abbrev Block (F : Type := Function) := Tree (Action F)

structure Dispatch where
  key : Key
  other : Option Key
  swapped : Bool
  deriving DecidableEq

/-- Exactly the supported two-arm source routing profiles. -/
inductive ValidDispatch : List (Key × Nat) → Option Nat → Dispatch → Prop where
  | one01 (key : Key) : ValidDispatch [(key, 0)] (some 1) ⟨key, none, false⟩
  | one10 (key : Key) : ValidDispatch [(key, 1)] (some 0) ⟨key, none, true⟩
  | two01 (first second : Key) :
      ValidDispatch [(first, 0), (second, 1)] none ⟨first, some second, false⟩
  | two10 (first second : Key) :
      ValidDispatch [(first, 1), (second, 0)] none ⟨first, some second, true⟩

def lowerDispatch : List (Key × Nat) → Option Nat → Option Dispatch
  | [(key, 0)], some 1 => some ⟨key, none, false⟩
  | [(key, 1)], some 0 => some ⟨key, none, true⟩
  | [(first, 0), (second, 1)], none => some ⟨first, some second, false⟩
  | [(first, 1), (second, 0)], none => some ⟨first, some second, true⟩
  | _, _ => none

theorem lowerDispatch_valid {cases : List (Key × Nat)} {fallback : Option Nat} {dispatch : Dispatch}
    (h : lowerDispatch cases fallback = some dispatch) : ValidDispatch cases fallback dispatch := by
  unfold lowerDispatch at h
  split at h <;> cases h <;> constructor

/-- The source follows the first matching key, then its explicit fallback. -/
def selectIndex (actual : Key) : List (Key × Nat) → Option Nat → Option Nat
  | [], fallback => fallback
  | (key, index) :: rest, fallback =>
    if actual = key then some index else selectIndex actual rest fallback

def selectSource (actual : Key) (cases : List (Key × Nat)) (fallback : Option Nat)
    (zero one : Unit → Option α) : Option α := do
  match ← selectIndex actual cases fallback with
  | 0 => zero ()
  | 1 => one ()
  | _ => none

theorem dispatch_preserves {cases : List (Key × Nat)} {fallback : Option Nat} {dispatch : Dispatch}
    (h : ValidDispatch cases fallback dispatch) (actual : Key) (zero one : Unit → Option α) :
    selectSource actual cases fallback zero one = selectBranch actual dispatch.key dispatch.other
      (if dispatch.swapped then one else zero) (if dispatch.swapped then zero else one) := by
  cases h with
  | one01 key | one10 key =>
    by_cases he : actual = key <;> simp [selectSource, selectIndex, selectBranch, he]
  | two01 first second | two10 first second =>
    by_cases hf : actual = first <;> by_cases hs : actual = second <;>
      simp_all [selectSource, selectIndex, selectBranch, eq_comm]

def lower {F : Type} : Block F → Option (Code F)
  | .done => some .done
  | .ret => some .ret
  | .step action rest => Code.step action.lower <$> lower rest
  | .switch scrutinee cases fallback zero one rest => do
    let dispatch ← lowerDispatch cases fallback
    let zero ← lower zero
    let one ← lower one
    let rest ← lower rest
    some (.branch scrutinee dispatch.key dispatch.other
      (if dispatch.swapped then one else zero) (if dispatch.swapped then zero else one) rest)

/-- Shared source-control execution. Primitive state, outcomes and work are
supplied by the language profile; routing and early return are implemented once. -/
def execWith {A S R C : Type}
    (instruction : S → A → Option (S × C))
    (scrutinee : S → Scrutinee → Option (Key × S))
    (returnValue : S → Option (R × C)) (finish : S → R) (nextState : R → Option S)
    (zero : C) (plus : C → C → C) (branchWork : Scrutinee → C) :
    Tree A → S → Option (R × C)
  | .done, state => some (finish state, zero)
  | .ret, state => returnValue state
  | .step action rest, state => do
    let (next, first) ← instruction state action
    let (result, last) ← execWith instruction scrutinee returnValue finish nextState zero plus branchWork rest next
    some (result, plus first last)
  | .switch scrut cases fallback left right rest, state => do
    let (actual, state) ← scrutinee state scrut
    let (result, first) ← selectSource actual cases fallback
      (fun _ => execWith instruction scrutinee returnValue finish nextState zero plus branchWork left state)
      (fun _ => execWith instruction scrutinee returnValue finish nextState zero plus branchWork right state)
    let charged := plus (branchWork scrut) first
    match nextState result with
    | none => some (result, charged)
    | some next =>
      let (result, last) ← execWith instruction scrutinee returnValue finish nextState zero plus branchWork rest next
      some (result, plus charged last)

def nextState : Outcome → Option Env
  | .next env => some env
  | .returned _ => none

def returnValue (env : Env) : Option (Outcome × Cost) := do
  let value ← env 0
  some (.returned value, ⟨1, {}⟩)

/-- Original snapshot profile of the shared executor. -/
def exec {F : Type} (call : CalleesFor F) : Block F → Env → Option (Outcome × Cost) :=
  execWith (fun env action => action.exec call env) evalScrutinee returnValue Outcome.next nextState
    {} Cost.plus (fun scrut => ⟨1 + scrut.weight, {}⟩)

theorem exec_done {F : Type} (call : CalleesFor F) (env : Env) : exec call .done env = some (.next env, {}) := rfl

theorem exec_ret {F : Type} (call : CalleesFor F) (env : Env) : exec call .ret env = returnValue env := rfl

theorem exec_step {F : Type} (call : CalleesFor F) (action : Action F) (rest : Block F) (env : Env) :
    exec call (.step action rest) env = (do
      let (next, first) ← action.exec call env
      let (result, last) ← exec call rest next
      some (result, first.plus last)) := rfl

theorem exec_switch {F : Type} (call : CalleesFor F) (scrut : Scrutinee) (cases : List (Key × Nat))
    (fallback : Option Nat) (left right rest : Block F) (env : Env) :
    exec call (.switch scrut cases fallback left right rest) env = (do
      let (actual, state) ← evalScrutinee env scrut
      let (result, first) ← selectSource actual cases fallback
        (fun _ => exec call left state) (fun _ => exec call right state)
      let charged := (⟨1 + scrut.weight, {}⟩ : Cost).plus first
      match result with
      | .returned value => some (.returned value, charged)
      | .next next =>
        let (result, last) ← exec call rest next
        some (result, charged.plus last)) := by
  simp only [exec, execWith]
  cases hs : evalScrutinee env scrut with
  | none => rfl
  | some pair =>
    rcases pair with ⟨actual, state⟩
    simp only [bind, Option.bind]
    cases hb : selectSource actual cases fallback _ _ with
    | none => rfl
    | some pair => rcases pair with ⟨result, first⟩; cases result <;> rfl

/-- Every supported source statement/control profile preserves complete results
and costs. This is equality before discarding the trace or work component. -/
theorem exec_lower {F : Type} (call : CalleesFor F) (source : Block F) (code : Code F)
    (hl : lower source = some code) (env : Env) : exec call source env = LookupSource.exec call code env := by
  induction source generalizing code env with
  | done => cases hl; rfl
  | ret => cases hl; rfl
  | step action rest ih =>
    cases hr : lower rest with
    | none => simp [lower, hr] at hl
    | some next =>
      simp only [lower, hr] at hl
      change some (Code.step action.lower next) = some code at hl
      have hcode := Option.some.inj hl
      subst code
      simp only [exec_step, LookupSource.exec, Action.exec]
      cases he : evalAction call env action.lower with
      | none => simp
      | some pair => simp [ih next hr]
  | switch scrutinee cases fallback zero one rest ihZero ihOne ihRest =>
    cases hd : lowerDispatch cases fallback with
    | none => simp [lower, hd] at hl
    | some dispatch =>
      cases hz : lower zero with
      | none => simp [lower, hd, hz] at hl
      | some cz =>
        cases ho : lower one with
        | none => simp [lower, hd, hz, ho] at hl
        | some co =>
          cases hr : lower rest with
          | none => simp [lower, hd, hz, ho, hr] at hl
          | some cr =>
            simp only [lower, hd, hz, ho, hr, bind, Option.bind, Option.some.injEq] at hl
            subst code
            simp only [exec_switch, LookupSource.exec]
            cases he : evalScrutinee env scrutinee with
            | none => simp
            | some pair =>
              rcases pair with ⟨actual, state⟩
              simp only [bind, Option.bind]
              rw [dispatch_preserves (lowerDispatch_valid hd)]
              cases hs : dispatch.swapped <;>
                simp only [Bool.false_eq_true, ite_false, ite_true,
                  ihZero cz hz, ihOne co ho, ihRest cr hr]
              all_goals rfl

/-- The call interpreter preserves the same supported source bodies at every
fuel, rather than only matching four hand-selected input examples. -/
def run (body : Function → Block) : Nat → Callees
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
      | .returned value => some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)

theorem run_succ (body : Function → Block) (fuel : Nat) (function : Function) (args : List Value) :
    run body (fuel + 1) function args =
      (if function = .boxNew then
        match args with
        | [value] => some (.boxed value, ⟨1, entryEvents function⟩)
        | _ => none
      else do
        let (outcome, cost) ← exec (run body fuel) (body function) (initialEnv args)
        match outcome with
        | .next _ => none
        | .returned value => some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)) := by rfl

theorem run_lower (source : Function → Block) (body : Function → Code)
    (hl : ∀ function, lower (source function) = some (body function))
    (fuel : Nat) (function : Function) (args : List Value) :
    run source fuel function args = LookupSource.run body fuel function args := by
  induction fuel generalizing function args with
  | zero => rfl
  | succ fuel ih =>
    have hc : run source fuel = LookupSource.run body fuel := funext fun f => funext fun a => ih f a
    rw [run_succ, LookupSource.run_succ]
    simp only [hc, exec_lower _ _ _ (hl function)]
    rfl

end SubtreeProofs.Rust.LookupSource.Control
