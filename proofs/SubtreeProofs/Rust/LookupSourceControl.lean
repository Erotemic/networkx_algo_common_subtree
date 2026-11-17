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

inductive Block (F : Type := Function) where
  | done : Block F
  | ret : Block F
  | step : Action F → Block F → Block F
  | switch : Scrutinee → List (Key × Nat) → Option Nat → Block F → Block F → Block F → Block F

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

/-- Normal-path source execution, including early return from a source arm.
Every local primitive and switch has the same explicit currency as the pilot. -/
def exec {F : Type} (call : CalleesFor F) : Block F → Env → Option (Outcome × Cost)
  | .done, env => some (.next env, {})
  | .ret, env => do
    let value ← env 0
    some (.returned value, ⟨1, {}⟩)
  | .step action rest, env => do
    let (next, first) ← action.exec call env
    let (result, last) ← exec call rest next
    some (result, first.plus last)
  | .switch scrutinee cases fallback zero one rest, env => do
    let (actual, state) ← evalScrutinee env scrutinee
    let (result, first) ← selectSource actual cases fallback
      (fun _ => exec call zero state) (fun _ => exec call one state)
    let charged := (⟨1 + scrutinee.weight, {}⟩ : Cost).plus first
    match result with
    | .returned value => some (.returned value, charged)
    | .next next =>
      let (result, last) ← exec call rest next
      some (result, charged.plus last)

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
      simp only [exec, LookupSource.exec, Action.exec]
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
            simp only [exec, LookupSource.exec]
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
