import Lax62Proofs.Refine.NREST.Pw
import SubtreeProofs.Rust.LookupSourceMutation

/-!
Timed-refinement interpretation of the same generated lookup source syntax.
This retains the existing operational C2 model and six work currencies. It
is not a compilation/representation theorem for the Lax word RAM or Rust heap.
-/

noncomputable section

namespace LaxSpike.SourceExecution

open Lax62Proofs.Refine
open SubtreeProofs.Rust.LookupSource

inductive Coin where
  | instruction | lookup | compare | copy | allocation | resultCopy
  deriving DecidableEq

abbrev Resource := ACost Coin ENat
abbrev Program (α : Type) := NRest α Resource

instance : Monad Program where
  pure := NRest.returnT
  bind := NRest.bindT

@[simp] theorem pure_def (value : α) :
    (pure value : Program α) = NRest.returnT value := rfl

@[simp] theorem bind_def (program : Program α) (next : α → Program β) :
    (program >>= next) = NRest.bindT program next := rfl

@[simp] theorem map_def (f : α → β) (program : Program α) :
    f <$> program = NRest.bindT program (fun value => NRest.returnT (f value)) := rfl

/-- Separate currencies are prices in the existing source-operation model,
not word-RAM instructions or a Rust allocator cost. -/
def encodeCost (cost : Cost) : Resource := ⟨fun
  | .instruction => cost.steps
  | .lookup => cost.events.lookupNodes
  | .compare => cost.events.compareNodes
  | .copy => cost.events.copyNodes
  | .allocation => cost.events.allocations
  | .resultCopy => cost.events.resultCopies⟩

@[simp] theorem encodeCost_zero : encodeCost {} = 0 := by
  apply ACost.toFun_injective
  funext coin
  cases coin <;> rfl

@[simp] theorem encodeCost_add (first second : Cost) :
    encodeCost (first.plus second) = encodeCost first + encodeCost second := by
  apply ACost.toFun_injective
  funext coin
  cases coin <;> simp [encodeCost, Cost.plus, SubtreeProofs.Rust.LookupEvents.Events.plus]

/-- Use the upstream timed primitive, retaining its own bind/refinement laws. -/
def charge (cost : Cost) (value : α) : Program α :=
  NRest.consume (NRest.returnT value) (encodeCost cost)

def fromOption (value : Option α) : Program α :=
  match value with
  | none => NRest.fail
  | some value => NRest.returnT value

/-- Specification interpretation of a source run, including explicit NRest.fail.
The interpreter below does not call this function or inspect the source run. -/
def encode : Option (α × Cost) → Program α
  | none => NRest.fail
  | some (value, cost) => charge cost value

private theorem bind_consume (program : Program α) (cost : Resource)
    (next : α → Program β) :
    NRest.bindT (NRest.consume program cost) next =
      NRest.consume (NRest.bindT program next) cost :=
  NRest.bindT_consume NRest.addSupContinuousB_acost program cost next

@[simp] theorem charge_bind (cost : Cost) (value : α) (next : α → Program β) :
    NRest.bindT (charge cost value) next = NRest.consume (next value) (encodeCost cost) := by
  rw [charge, bind_consume, NRest.returnT_bindT]

/-- Exact timed composition, supplied by upstream consumption/bind laws and
additivity of the source-cost encoding. -/
theorem encode_bind (first : Option (α × Cost)) (next : α → Option (β × Cost)) :
    NRest.bindT (encode first) (fun value => encode (next value)) =
      encode (do
        let (value, before) ← first
        let (result, after) ← next value
        pure (result, before.plus after)) := by
  cases first with
  | none => simp [encode]
  | some pair =>
    rcases pair with ⟨value, before⟩
    cases hn : next value with
    | none => simp [encode, hn, charge, bind_consume]
    | some pair =>
      rcases pair with ⟨result, after⟩
      simp [encode, hn, charge, bind_consume, NRest.consume_consume]

abbrev Callees := Function → List Value → Program Value

/-- Primitive expression reads pay the syntax-derived source-operation weight;
callee work is composed by the timed monad rather than computed for free. -/
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
    | some _ => NRest.fail

/-- The existing generated syntax drives this independent timed interpreter.
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
      else if other.all (· = actual) then execute call no env else NRest.fail
    match result with
    | .returned value => pure (.returned value)
    | .next env => execute call rest env

/-- Entry packets and Box creation retain the source model's currencies.
Fuel only controls nesting; it is never used as an estimate of work. -/
def run (body : Function → Code) : Nat → Callees
  | 0, _, _ => NRest.fail
  | fuel + 1, function, args => do
    let _ ← charge ⟨1, entryEvents function⟩ ()
    if function = .boxNew then
      match args with
      | [value] => pure (.boxed value)
      | _ => NRest.fail
    else
      let result ← execute (run body fuel) (body function) (initialEnv args)
      match result with
      | .next _ => NRest.fail
      | .returned value => pure value


/-- Action interpretation is exact under exact callee interpretation, using
upstream timed bind rather than assuming the final resource bound. -/
theorem action_exact (call : Callees)
    (source : SubtreeProofs.Rust.LookupSource.Callees)
    (hc : ∀ function args, call function args = encode (source function args))
    (env : Env) (instruction : Action) :
    action call env instruction = encode (evalAction source env instruction) := by
  cases instruction with
  | scope slot => simp [action, evalAction, encode, charge, bind_consume]
  | assign slot expression =>
    cases he : evalRValue env expression with
    | none => simp [action, evalAction, encode, fromOption, charge, bind_consume, he]
    | some pair =>
      rcases pair with ⟨value, next⟩
      simp [action, evalAction, encode, fromOption, charge, bind_consume, he]
  | call function args slot =>
    cases he : evalOperands args env with
    | none => simp [action, evalAction, encode, fromOption, charge, bind_consume, he]
    | some pair =>
      rcases pair with ⟨values, next⟩
      cases hs : source function values with
      | none => simp [action, evalAction, encode, fromOption, charge, bind_consume, he, hc, hs]
      | some pair =>
        rcases pair with ⟨value, cost⟩
        simp [action, evalAction, encode, fromOption, charge, bind_consume,
          NRest.consume_consume, he, hc, hs]
  | dropMoved slot =>
    cases he : env slot with
    | none => simp [action, evalAction, encode, charge, bind_consume, he]
    | some value => simp [action, evalAction, encode, charge, bind_consume, he]

/-- Exact timed interpretation covers the selected arm, early return and
common continuation. No source instruction is inferred from recursion depth. -/
theorem execute_exact (call : Callees)
    (source : SubtreeProofs.Rust.LookupSource.Callees)
    (hc : ∀ function args, call function args = encode (source function args))
    (code : Code) (env : Env) :
    execute call code env = encode (SubtreeProofs.Rust.LookupSource.exec source code env) := by
  induction code generalizing env with
  | done => simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, charge]
  | ret =>
    cases he : env 0 <;>
      simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption, charge,
        bind_consume, he]
  | step instruction rest ih =>
    simp only [execute, bind_def, action_exact call source hc, ih, encode_bind]
    rfl
  | branch scrutinee key other yes no rest ihYes ihNo ihRest =>
    cases hs : evalScrutinee env scrutinee with
    | none =>
      simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption, charge,
        bind_consume, hs]
    | some pair =>
      rcases pair with ⟨actual, next⟩
      by_cases hk : actual = key
      · cases hx : SubtreeProofs.Rust.LookupSource.exec source yes next with
        | none =>
          simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
            charge, bind_consume, hs, selectBranch, hk, ihYes, hx]
        | some pair =>
          rcases pair with ⟨outcome, cost⟩
          cases outcome with
          | returned value =>
            simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
              charge, bind_consume, NRest.consume_consume, hs, selectBranch, hk, ihYes, hx]
          | next state =>
            cases ht : SubtreeProofs.Rust.LookupSource.exec source rest state <;>
              simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
                charge, bind_consume, NRest.consume_consume, hs, selectBranch, hk,
                ihYes, ihRest, hx, ht, add_assoc]
      · by_cases ho : other.all (· = actual) = true
        · cases hx : SubtreeProofs.Rust.LookupSource.exec source no next with
          | none =>
            simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
              charge, bind_consume, hs, selectBranch, hk, ho, ihNo, hx]
          | some pair =>
            rcases pair with ⟨outcome, cost⟩
            cases outcome with
            | returned value =>
              simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
                charge, bind_consume, NRest.consume_consume, hs, selectBranch, hk, ho, ihNo, hx]
            | next state =>
              cases ht : SubtreeProofs.Rust.LookupSource.exec source rest state <;>
                simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
                  charge, bind_consume, NRest.consume_consume, hs, selectBranch, hk, ho,
                  ihNo, ihRest, hx, ht, add_assoc]
        · simp [execute, SubtreeProofs.Rust.LookupSource.exec, encode, fromOption,
            charge, bind_consume, hs, selectBranch, hk, ho]

/-- The full timed interpretation equals the original successful-run semantics
at every fuel, retaining all six currencies rather than only the returned value. -/
theorem run_exact (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) :
    run body fuel function args =
      encode (SubtreeProofs.Rust.LookupSource.run body fuel function args) := by
  induction fuel generalizing function args with
  | zero => rfl
  | succ fuel ih =>
    by_cases hf : function = .boxNew
    · subst function
      cases args with
      | nil => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume]
      | cons first rest =>
        cases rest with
        | nil => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume]
        | cons _ _ => simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume]
    · have he := execute_exact (run body fuel)
        (SubtreeProofs.Rust.LookupSource.run body fuel) ih (body function) (initialEnv args)
      cases hx : SubtreeProofs.Rust.LookupSource.exec
          (SubtreeProofs.Rust.LookupSource.run body fuel) (body function) (initialEnv args) with
      | none =>
        simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume, hf, he, hx]
      | some pair =>
        rcases pair with ⟨outcome, cost⟩
        cases outcome with
        | next env =>
          simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume, hf, he, hx]
        | returned value =>
          simp [run, SubtreeProofs.Rust.LookupSource.run_succ, encode, charge, bind_consume,
            NRest.consume_consume, hf, he, hx]

/-- Existing NREST specification order separates the independent result
predicate from a currency-by-currency resource envelope. -/
theorem charge_le_spec (cost : Cost) (value : α) (post : α → Prop)
    (budget : α → Resource) :
    charge cost value ≤ NRest.spec post budget ↔
      post value ∧ encodeCost cost ≤ budget value := by
  classical
  simp only [charge, NRest.consume_returnT, NRest.spec, NRest.rest_le_rest_iff,
    NRest.single_le_iff]
  by_cases hp : post value <;> simp [hp]

/-- A successful source run gives an exact singleton timed computation and
rules out NREST failure, in addition to preserving every cost currency. -/
theorem run_success (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Value) {value : Value} {cost : Cost}
    (hr : SubtreeProofs.Rust.LookupSource.run body fuel function args = some (value, cost)) :
    run body fuel function args = charge cost value ∧
      NRest.nofailT (run body fuel function args) := by
  rw [run_exact, hr]
  simp [encode, charge, NRest.consume_returnT]

/-- The existing instruction theorem supplies a finite, pointwise envelope;
all five packet currencies keep their exact source counts. -/
theorem program_spec (function : Function) (args : List Value) (fuel : Nat)
    {value : Value} {cost : Cost}
    (hr : SubtreeProofs.Rust.LookupSource.run
      SubtreeProofs.Rust.LookupSource.Program.body fuel function args = some (value, cost)) :
    run SubtreeProofs.Rust.LookupSource.Program.body fuel function args ≤
      NRest.spec (fun result => result = value)
        (fun _ => encodeCost ⟨256 * cost.events.units, cost.events⟩) := by
  rw [(run_success _ _ _ _ hr).1]
  apply (charge_le_spec _ _ _ _).2
  refine ⟨rfl, ACost.le_def.mpr ?_⟩
  intro coin
  cases coin
  · change (cost.steps : ENat) ≤ ((256 * cost.events.units : Nat) : ENat)
    exact_mod_cast program_source_bound hr
  all_goals simp [encodeCost]

/-- Independent first-hit value and the same instruction/packet envelope as
the native and charged pilots, in the upstream refinement order. -/
theorem lookup_spec (table : verified_ordered_core.MemoTable)
    (left right : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) :
    run SubtreeProofs.Rust.LookupSource.Program.body fuel .lookup
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] ≤
      NRest.spec (fun result => result = encodeOption
        (SubtreeProofs.Rust.MemoizedOrderedSolver.findResult table left right))
        (fun _ => encodeCost ⟨256 * (SubtreeProofs.Rust.LookupEvents.lookup table left right).2.units,
          (SubtreeProofs.Rust.LookupEvents.lookup table left right).2⟩) := by
  obtain ⟨cost, hr, hc⟩ := lookup_source table left right fuel hf
  simpa only [hc, SubtreeProofs.Rust.LookupEvents.lookup_value] using program_spec _ _ _ hr

theorem compare_spec (left right : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : wordHeight left ≤ fuel) :
    run SubtreeProofs.Rust.LookupSource.Program.body fuel .compare
      [.reference (encodeWord left), .reference (encodeWord right)] ≤
      NRest.spec (fun result => result = .boolean (decide (left = right)))
        (fun _ => encodeCost ⟨256 * (SubtreeProofs.Rust.LookupEvents.compare left right).2,
          ⟨0, (SubtreeProofs.Rust.LookupEvents.compare left right).2, 0, 0, 0⟩⟩) := by
  obtain ⟨cost, hr, hc⟩ := compare_source left right fuel hf
  simpa only [hc, SubtreeProofs.Rust.LookupEvents.compare_value,
    SubtreeProofs.Rust.LookupEvents.Events.units, Nat.zero_add, Nat.add_zero] using program_spec _ _ _ hr

theorem copy_spec (word : verified_ordered_core.BalancedWord) (fuel : Nat)
    (hf : wordHeight word ≤ fuel) :
    run SubtreeProofs.Rust.LookupSource.Program.body fuel .copyWord [.reference (encodeWord word)] ≤
      NRest.spec (fun result => result = encodeWord word)
        (fun _ => encodeCost ⟨256 * (SubtreeProofs.Rust.LookupEvents.copy word).2.units,
          (SubtreeProofs.Rust.LookupEvents.copy word).2⟩) := by
  obtain ⟨cost, hr, hc⟩ := copy_source word fuel hf
  simpa only [hc] using program_spec _ _ _ hr

theorem copyResult_spec (result : verified_ordered_core.CommonEmbedding) (fuel : Nat)
    (hf : wordHeight result.word + 1 ≤ fuel) :
    run SubtreeProofs.Rust.LookupSource.Program.body fuel .copyResult [.reference (encodeResult result)] ≤
      NRest.spec (fun value => value = encodeResult result)
        (fun _ => encodeCost ⟨256 * (SubtreeProofs.Rust.LookupEvents.copyResult result).2.units,
          (SubtreeProofs.Rust.LookupEvents.copyResult result).2⟩) := by
  obtain ⟨cost, hr, hc⟩ := copyResult_source result fuel hf
  simpa only [hc] using program_spec _ _ _ hr

/-- Only the comparison currency is constrained; other resources may be
arbitrarily large, so rejecting this budget cannot rely on aggregate slack. -/
def zeroComparisonBudget : Resource := ⟨fun coin =>
  match coin with
  | .compare => 0
  | _ => ⊤⟩

theorem original_empty_meets_zero_compare :
    run SubtreeProofs.Rust.LookupSource.Program.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty), .reference (encodeWord .Empty)] ≤
      NRest.spec (fun result => result = encodeOption none) (fun _ => zeroComparisonBudget) := by
  obtain ⟨cost, hr, hc⟩ := lookup_source .Empty .Empty .Empty 3 (by decide)
  rw [(run_success _ _ _ _ hr).1]
  apply (charge_le_spec _ _ _ _).2
  refine ⟨rfl, ACost.le_def.mpr ?_⟩
  intro coin
  cases coin <;> simp [encodeCost, zeroComparisonBudget, hc,
    SubtreeProofs.Rust.LookupEvents.lookup]

/-- The actual compiled mutant preserves the answer but fails the original
empty-table contract in the upstream timed-refinement order. -/
theorem extra_compare_violates_old_budget :
    ¬run ExtraCompare.body 3 .lookup
      [.reference (encodeTable .Empty), .reference (encodeWord .Empty), .reference (encodeWord .Empty)] ≤
      NRest.spec (fun result => result = encodeOption none) (fun _ => zeroComparisonBudget) := by
  obtain ⟨cost, hr, hc⟩ := extra_compare_execution
  rw [(run_success _ _ _ _ hr).1]
  intro h
  have hb := ((charge_le_spec _ _ _ _).1 h).2
  have hcompare := (ACost.le_def.mp hb) .compare
  simp [encodeCost, zeroComparisonBudget, hc] at hcompare

#check @run_exact
#check @lookup_spec
#check @compare_spec
#check @copy_spec
#check @copyResult_spec
#check @original_empty_meets_zero_compare
#check @extra_compare_violates_old_budget

#print axioms action_exact
#print axioms execute_exact
#print axioms run_exact
#print axioms run_success
#print axioms lookup_spec
#print axioms compare_spec
#print axioms copy_spec
#print axioms copyResult_spec
#print axioms original_empty_meets_zero_compare
#print axioms extra_compare_violates_old_budget

end LaxSpike.SourceExecution
