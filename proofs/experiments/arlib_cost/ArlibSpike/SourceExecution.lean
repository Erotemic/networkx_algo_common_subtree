import Arlib.Computation.Charged
import SubtreeProofs.Rust.LookupSourceMutation

/-!
A charged interpretation of the existing read-only source-operation model.
The work currencies retain instruction/access work and each packet separately;
they are not added together into a hardware-time claim. This is not a RAM
representation theorem. Shared references and primitive reads retain the
operational model's existing interpretation boundary.
-/

namespace ArlibSpike.SourceExecution

open Arlib.Computation (Charged CostVec)
open SubtreeProofs.Rust.LookupSource

inductive Coin where
  | instruction | lookup | compare | copy | allocation | resultCopy
  deriving DecidableEq

abbrev Program (α : Type) := OptionT (Charged Coin Unit) α

/-- Charge one represented source operation, preserving separate currencies. -/
def charge (cost : Cost) (value : α) : Program α := OptionT.mk do
  let _ ← Charged.opMany .instruction cost.steps ()
  let _ ← Charged.opMany .lookup cost.events.lookupNodes ()
  let _ ← Charged.opMany .compare cost.events.compareNodes ()
  let _ ← Charged.opMany .copy cost.events.copyNodes ()
  let _ ← Charged.opMany .allocation cost.events.allocations ()
  let _ ← Charged.opMany .resultCopy cost.events.resultCopies ()
  pure (some value)

/-- Decode a tally only in specifications, never during execution. -/
def decode (tally : CostVec Coin) : Cost :=
  ⟨tally .instruction, ⟨tally .lookup, tally .compare, tally .copy,
    tally .allocation, tally .resultCopy⟩⟩

noncomputable def observe (program : Program α) : Option (α × Cost) :=
  program.val.map (fun value => (value, decode program.cost))

theorem decode_add (first second : CostVec Coin) :
    decode (first + second) = (decode first).plus (decode second) := rfl

@[simp] theorem observe_pure (value : α) :
    observe (pure value : Program α) = some (value, {}) := rfl

@[simp] theorem observe_charge (cost : Cost) (value : α) :
    observe (charge cost value) = some (value, cost) := by
  cases cost with
  | mk steps events =>
    cases events
    simp [observe, charge, decode, OptionT.mk, CostVec.many]

@[simp] theorem observe_failure :
    observe (failure : Program α) = none := rfl

private theorem raw_val_bind (p : Charged Coin Unit α)
    (f : α → Charged Coin Unit β) :
    (Charged.bind p f).val = (f p.val).val := Charged.val_bind p f

private theorem raw_cost_bind (p : Charged Coin Unit α)
    (f : α → Charged Coin Unit β) :
    (Charged.bind p f).cost = p.cost + (f p.val).cost := Charged.cost_bind p f

/-- Successful bind preserves both source costs; failure is outside this
successful-execution observation, as in the original source interpreter. -/
theorem observe_bind (first : Program α) (next : α → Program β) :
    observe (first >>= next) = (do
      let (value, before) ← observe first
      let (result, after) ← observe (next value)
      pure (result, before.plus after)) := by
  cases h : first.val with
  | none => simp [observe, bind, OptionT.bind, OptionT.mk, raw_val_bind, raw_cost_bind, h]
  | some value =>
    cases hn : (next value).val with
    | none => simp [observe, bind, OptionT.bind, OptionT.mk, raw_val_bind, raw_cost_bind, h, hn]
    | some result => simp [observe, bind, OptionT.bind, OptionT.mk, raw_val_bind, raw_cost_bind, h, hn, decode_add]

/-- Local source expressions are interpreted at the explicit instruction price
of their calling syntax node, rather than treated as a unit structural lookup. -/
def fromOption (value : Option α) : Program α :=
  match value with
  | none => failure
  | some value => pure value

@[simp] theorem observe_fromOption (value : Option α) :
    observe (fromOption value) = value.map (fun result => (result, {})) := by
  cases value <;> rfl

abbrev Callees := Function → List Value → Program Value

/-- Primitive expression reads pay the syntax-derived source-operation weight;
callee work is composed by the charged monad rather than computed for free. -/
def action (call : Callees) (env : Env) (instruction : Action) : Program Env := do
  let _ ← charge ⟨instruction.weight, {}⟩ ()
  match instruction with
  | .scope slot => pure (env.set slot none)
  | .assign slot expression =>
    let (value, env) ← fromOption (evalRValue env expression)
    pure (env.set slot (some value))
  | .call function args slot =>
    let (values, env) ← fromOption (evalOperands args env)
    let value ← call function values
    pure (env.set slot (some value))
  | .dropMoved slot =>
    match env slot with
    | none => pure env
    | some _ => failure

/-- The existing generated syntax drives this independent charged interpreter.
Branches charge only the selected arm and stop at a source return. -/
def execute (call : Callees) : Code → Env → Program Outcome
  | .done, env => pure (.next env)
  | .ret, env => do
    let _ ← charge ⟨1, {}⟩ ()
    let value ← fromOption (env 0)
    pure (.returned value)
  | .step instruction rest, env => do
    let env ← action call env instruction
    execute call rest env
  | .branch scrutinee key other yes no rest, env => do
    let _ ← charge ⟨1 + scrutinee.weight, {}⟩ ()
    let (actual, env) ← fromOption (evalScrutinee env scrutinee)
    let result ← if actual = key then execute call yes env
      else if other.all (· = actual) then execute call no env else failure
    match result with
    | .returned value => pure (.returned value)
    | .next env => execute call rest env

/-- Entry packets and Box creation retain the source model's currencies.
Fuel only controls nesting; it is never used as an estimate of work. -/
def run (body : Function → Code) : Nat → Callees
  | 0, _, _ => failure
  | fuel + 1, function, args => do
    let _ ← charge ⟨1, entryEvents function⟩ ()
    if function = .boxNew then
      match args with
      | [value] => pure (.boxed value)
      | _ => failure
    else
      let result ← execute (run body fuel) (body function) (initialEnv args)
      match result with
      | .next _ => failure
      | .returned value => pure value

private theorem zero_plus (cost : Cost) : ({} : Cost).plus cost = cost := by
  cases cost with
  | mk steps events => cases events; simp [Cost.plus, SubtreeProofs.Rust.LookupEvents.Events.plus]

private theorem plus_zero (cost : Cost) : cost.plus {} = cost := by
  cases cost with
  | mk steps events => cases events; simp [Cost.plus, SubtreeProofs.Rust.LookupEvents.Events.plus]

private theorem plus_assoc (a b c : Cost) : (a.plus b).plus c = a.plus (b.plus c) := by
  simp [Cost.plus, SubtreeProofs.Rust.LookupEvents.Events.plus, Nat.add_assoc]

@[simp] theorem observe_map (f : α → β) (program : Program α) :
    observe (f <$> program) = (observe program).map (fun pair => (f pair.1, pair.2)) := by
  rw [← bind_pure_comp, observe_bind]
  cases h : observe program with
  | none => simp
  | some pair =>
    rcases pair with ⟨value, cost⟩
    simp [plus_zero]

/-- Exact value and complete resource correspondence for each action, under
exact callee correspondence. This does not assume a whole-program bound. -/
theorem action_observe (call : Callees)
    (source : SubtreeProofs.Rust.LookupSource.Callees)
    (hc : ∀ function args, observe (call function args) = source function args)
    (env : Env) (instruction : Action) :
    observe (action call env instruction) = evalAction source env instruction := by
  cases instruction with
  | scope slot => simp [action, evalAction]
  | assign slot expression =>
    cases he : evalRValue env expression with
    | none => simp [action, evalAction, observe_bind, he]
    | some pair =>
      rcases pair with ⟨value, next⟩
      simp [action, evalAction, observe_bind, he, plus_zero]
  | call function args slot =>
    cases he : evalOperands args env with
    | none => simp [action, evalAction, observe_bind, he]
    | some pair =>
      rcases pair with ⟨values, next⟩
      cases hs : source function values with
      | none => simp [action, evalAction, observe_bind, he, hc, hs]
      | some pair =>
        rcases pair with ⟨value, cost⟩
        simp [action, evalAction, observe_bind, he, hc, hs, zero_plus]
  | dropMoved slot =>
    cases he : env slot with
    | none => simp [action, evalAction, he]
    | some value => simp [action, evalAction, observe_bind, he]

/-- Syntax-directed exact correspondence covers both selected-arm early return
and continuation, including all charged recursive calls. -/
theorem execute_observe (call : Callees)
    (source : SubtreeProofs.Rust.LookupSource.Callees)
    (hc : ∀ function args, observe (call function args) = source function args)
    (code : Code) (env : Env) :
    observe (execute call code env) = SubtreeProofs.Rust.LookupSource.exec source code env := by
  induction code generalizing env with
  | done => rfl
  | ret =>
    cases he : env 0 <;>
      simp [execute, SubtreeProofs.Rust.LookupSource.exec, observe_bind, he, plus_zero]
  | step instruction rest ih =>
    simp only [execute, observe_bind, action_observe call source hc]
    cases he : evalAction source env instruction with
    | none => simp [SubtreeProofs.Rust.LookupSource.exec, he]
    | some pair =>
      rcases pair with ⟨next, cost⟩
      simp [SubtreeProofs.Rust.LookupSource.exec, he, ih]
  | branch scrutinee key other yes no rest ihYes ihNo ihRest =>
    cases hs : evalScrutinee env scrutinee with
    | none => simp [execute, SubtreeProofs.Rust.LookupSource.exec, observe_bind, hs]
    | some pair =>
      rcases pair with ⟨actual, next⟩
      by_cases hk : actual = key
      · simp only [execute, observe_bind, observe_charge, observe_fromOption,
          SubtreeProofs.Rust.LookupSource.exec, hs, selectBranch, hk]
        cases hx : SubtreeProofs.Rust.LookupSource.exec source yes next with
        | none => simp [observe_bind, ihYes, hx]
        | some pair =>
          rcases pair with ⟨outcome, cost⟩
          cases outcome with
          | returned value => simp [observe_bind, ihYes, hx, plus_zero, zero_plus]
          | next state =>
            cases ht : SubtreeProofs.Rust.LookupSource.exec source rest state <;>
              simp [observe_bind, ihYes, ihRest, hx, ht, zero_plus, plus_assoc]
      · by_cases ho : other.all (· = actual) = true
        · simp only [execute, observe_bind, observe_charge, observe_fromOption,
            SubtreeProofs.Rust.LookupSource.exec, hs, selectBranch]
          cases hx : SubtreeProofs.Rust.LookupSource.exec source no next with
          | none => simp [observe_bind, hk, ho, ihNo, hx]
          | some pair =>
            rcases pair with ⟨outcome, cost⟩
            cases outcome with
            | returned value => simp [observe_bind, hk, ho, ihNo, hx, plus_zero, zero_plus]
            | next state =>
              cases ht : SubtreeProofs.Rust.LookupSource.exec source rest state <;>
                simp [observe_bind, hk, ho, ihNo, ihRest, hx, ht, zero_plus, plus_assoc]
        · simp [execute, SubtreeProofs.Rust.LookupSource.exec, observe_bind, hs,
            selectBranch, hk, ho]

/-- Every successful charged execution has exactly the operational value,
instruction count and five packet counts, for arbitrary generated bodies. -/
theorem run_observe (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) :
    observe (run body fuel function args) =
      SubtreeProofs.Rust.LookupSource.run body fuel function args := by
  induction fuel generalizing function args with
  | zero => rfl
  | succ fuel ih =>
    by_cases hf : function = .boxNew
    · subst function
      cases args with
      | nil => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, observe_bind]
      | cons first rest =>
        cases rest with
        | nil => simp [run, SubtreeProofs.Rust.LookupSource.run_succ]
        | cons _ _ => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, observe_bind]
    · have he := execute_observe (run body fuel)
        (SubtreeProofs.Rust.LookupSource.run body fuel) ih (body function) (initialEnv args)
      cases hx : SubtreeProofs.Rust.LookupSource.exec
          (SubtreeProofs.Rust.LookupSource.run body fuel) (body function) (initialEnv args) with
      | none => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, observe_bind, hf, he, hx]
      | some pair =>
        rcases pair with ⟨outcome, cost⟩
        cases outcome with
        | next env => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, observe_bind, hf, he, hx]
        | returned value =>
          simp [run, SubtreeProofs.Rust.LookupSource.run_succ, observe_bind, hf, he, hx, plus_zero]

/-- Exact correspondence exposes the charged result and every currency
without inspecting costs during the interpreted source computation. -/
theorem source_run_agrees (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) {value : Value} {cost : Cost}
    (hr : SubtreeProofs.Rust.LookupSource.run body fuel function args = some (value, cost)) :
    (run body fuel function args).val = some value ∧
      decode (run body fuel function args).cost = cost := by
  have h := (run_observe body fuel function args).trans hr
  cases hv : (run body fuel function args).val with
  | none => simp [observe, hv] at h
  | some actual =>
    have hp : actual = value ∧ decode (run body fuel function args).cost = cost := by
      simpa [observe, hv] using h
    exact ⟨congrArg some hp.1, hp.2⟩

/-- Transfer the source interpreter's proved instruction envelope, keeping the
exact packet currencies and independent result available to consumers. -/
theorem program_spec (function : Function) (args : List Value) (fuel : Nat)
    {value : Value} {cost : Cost}
    (hr : SubtreeProofs.Rust.LookupSource.run
      SubtreeProofs.Rust.LookupSource.Program.body fuel function args = some (value, cost)) :
    let computation := run SubtreeProofs.Rust.LookupSource.Program.body fuel function args
    computation.val = some value ∧ (decode computation.cost).events = cost.events ∧
      computation.cost .instruction ≤ 256 * cost.events.units := by
  obtain ⟨hv, he⟩ := source_run_agrees _ _ _ _ hr
  exact ⟨hv, congrArg Cost.events he,
    le_of_eq_of_le (congrArg Cost.steps he) (program_source_bound hr)⟩

/-- The same independent first-hit lookup contract and instruction envelope
as the native WP pilot, with all structural packets retained separately. -/
theorem lookup_spec (table : verified_ordered_core.MemoTable)
    (left right : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    let computation := run SubtreeProofs.Rust.LookupSource.Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)]
    computation.val = some (encodeOption
      (SubtreeProofs.Rust.MemoizedOrderedSolver.findResult table left right)) ∧
    (decode computation.cost).events = (SubtreeProofs.Rust.LookupEvents.lookup table left right).2 ∧
    computation.cost .instruction ≤ 256 * (SubtreeProofs.Rust.LookupEvents.lookup table left right).2.units := by
  obtain ⟨cost, hr, hc⟩ := lookup_source table left right fuel hf
  obtain ⟨hv, he, hb⟩ := program_spec _ _ _ hr
  refine ⟨?_, he.trans hc, ?_⟩
  · simpa only [SubtreeProofs.Rust.LookupEvents.lookup_value] using hv
  · simpa only [hc] using hb

/-- The structural scan has the independent equality result and preserves its
short-circuit comparison count, rather than treating a whole key as one step. -/
theorem compare_spec (left right : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : wordHeight left ≤ fuel) :
    let computation := run SubtreeProofs.Rust.LookupSource.Program.body fuel .compare
      [.reference (encodeWord left), .reference (encodeWord right)]
    computation.val = some (.boolean (decide (left = right))) ∧
    (decode computation.cost).events =
      ⟨0, (SubtreeProofs.Rust.LookupEvents.compare left right).2, 0, 0, 0⟩ ∧
    computation.cost .instruction ≤ 256 * (SubtreeProofs.Rust.LookupEvents.compare left right).2 := by
  obtain ⟨cost, hr, hc⟩ := compare_source left right fuel hf
  obtain ⟨hv, he, hb⟩ := program_spec _ _ _ hr
  refine ⟨?_, he.trans hc, ?_⟩
  · simpa only [SubtreeProofs.Rust.LookupEvents.compare_value] using hv
  · simpa only [hc, SubtreeProofs.Rust.LookupEvents.Events.units, Nat.zero_add, Nat.add_zero] using hb

theorem copy_spec (word : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : wordHeight word ≤ fuel) :
    let computation := run SubtreeProofs.Rust.LookupSource.Program.body fuel .copyWord
      [.reference (encodeWord word)]
    computation.val = some (encodeWord word) ∧
    (decode computation.cost).events = (SubtreeProofs.Rust.LookupEvents.copy word).2 ∧
    computation.cost .instruction ≤ 256 * (SubtreeProofs.Rust.LookupEvents.copy word).2.units := by
  obtain ⟨cost, hr, hc⟩ := copy_source word fuel hf
  obtain ⟨hv, he, hb⟩ := program_spec _ _ _ hr
  exact ⟨hv, he.trans hc, by simpa only [hc] using hb⟩

theorem copyResult_spec (result : verified_ordered_core.CommonEmbedding) (fuel : Nat)
    (hf : wordHeight result.word + 1 ≤ fuel) :
    let computation := run SubtreeProofs.Rust.LookupSource.Program.body fuel .copyResult
      [.reference (encodeResult result)]
    computation.val = some (encodeResult result) ∧
    (decode computation.cost).events = (SubtreeProofs.Rust.LookupEvents.copyResult result).2 ∧
    computation.cost .instruction ≤ 256 * (SubtreeProofs.Rust.LookupEvents.copyResult result).2.units := by
  obtain ⟨cost, hr, hc⟩ := copyResult_source result fuel hf
  obtain ⟨hv, he, hb⟩ := program_spec _ _ _ hr
  exact ⟨hv, he.trans hc, by simpa only [hc] using hb⟩

/-- The source mutant's actual charged comparison count is nonzero on empty
input, rejecting the old empty-table comparison budget. -/
theorem extra_compare_violates_old_budget :
    let computation := run ExtraCompare.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty), .reference (encodeWord .Empty)]
    computation.val = some (encodeOption none) ∧ ¬computation.cost .compare ≤ 0 := by
  obtain ⟨cost, hr, hc⟩ := extra_compare_execution
  obtain ⟨hv, he⟩ := source_run_agrees _ _ _ _ hr
  refine ⟨hv, ?_⟩
  have h := congrArg (fun cost : Cost => cost.events.compareNodes) he
  change _ = cost.events.compareNodes at h
  rw [hc] at h
  simp only [decode] at h
  rw [h]
  decide

#print axioms action_observe
#print axioms execute_observe
#print axioms run_observe
#print axioms lookup_spec
#print axioms compare_spec
#print axioms copy_spec
#print axioms copyResult_spec
#print axioms extra_compare_violates_old_budget

end ArlibSpike.SourceExecution
