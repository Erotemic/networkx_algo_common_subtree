module

public import SubtreeProofs.Rust.LookupSourceControl

/-! The concatenation/insertion source pilot reuses the same primitive and
control semantics with its own function set. Every local instruction still
contributes to `Cost.steps`; the existing event fields retain their meanings.
The larger evaluator and stack borrows are separate subsequent obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource

open LookupSource

inductive Function where
  | copyWord | copyResult | concatenate | insert | boxNew
  deriving DecidableEq, Repr

abbrev Code := LookupSource.Code Function
abbrev Block := Control.Block Function
abbrev Calls := CalleesFor Function

def arity : Function → Nat
  | .copyWord | .copyResult | .boxNew => 1
  | .concatenate => 2
  | .insert => 4

def entryEvents : Function → LookupEvents.Events
  | .copyWord => { copyNodes := 1 }
  | .copyResult => { resultCopies := 1 }
  | .boxNew => { allocations := 1 }
  | .concatenate | .insert => {}

/-- Function entry costs one step. New helper entries have no new marker in
lookup's event projection; their full instruction costs remain in `steps`. -/
def runWith (execute : Calls → Function → Env → Option (Outcome × Cost)) : Nat → Calls
  | 0, _, _ => none
  | fuel + 1, function, args =>
    if function = .boxNew then
      match args with
      | [value] => some (.boxed value, ⟨1, entryEvents function⟩)
      | _ => none
    else do
      let (outcome, cost) ← execute (runWith execute fuel) function (initialEnv args)
      match outcome with
      | .next _ => none
      | .returned value => some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)

def run (body : Function → Code) : Nat → Calls :=
  runWith (fun call function => LookupSource.exec call (body function))

theorem run_succ (body : Function → Code) (fuel : Nat) (function : Function) (args : List Value) :
    run body (fuel + 1) function args =
      (if function = .boxNew then
        match args with
        | [value] => some (.boxed value, ⟨1, entryEvents function⟩)
        | _ => none
      else do
        let (outcome, cost) ← LookupSource.exec (run body fuel) (body function) (initialEnv args)
        match outcome with
        | .next _ => none
        | .returned value => some (value, (⟨1, entryEvents function⟩ : Cost).plus cost)) := rfl

def sourceRun (body : Function → Block) : Nat → Calls :=
  runWith (fun call function => Control.exec call (body function))

/-- Complete execution and cost equality follows for every fuel and argument
list, without assuming any functional specification of either helper. -/
theorem run_lower (source : Function → Block) (body : Function → Code)
    (hl : ∀ function, Control.lower (source function) = some (body function)) :
    sourceRun source = run body := by
  have he : (fun call function => Control.exec call (source function)) =
      (fun call function => LookupSource.exec call (body function)) := by
    funext call function env
    exact Control.exec_lower call _ _ (hl function) env
  exact congrArg runWith he

end SubtreeProofs.Rust.MemoSource
