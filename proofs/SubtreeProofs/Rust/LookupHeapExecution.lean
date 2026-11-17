module

public import SubtreeProofs.Rust.LookupHeapPrimitives

/-! Addressed execution of the certified lookup instruction language. Every
source currency is retained. Memory grows only at Box creation. Storage reset
invalidates locals; this model has no stack pointers and does not yet prove
unique ownership or destruction/physical residency. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

abbrev Calls := Function → List Cell → Memory → Option (Cell × Memory × Cost)

def action (call : Calls) (memory : Memory) (env : Locals) (instruction : Action) :
    Option (Locals × Memory × Cost) := do
  match instruction with
  | .scope slot => some (env.set slot none, memory, ⟨instruction.weight, {}⟩)
  | .assign slot rhs =>
    let (value, env) ← rvalue memory env rhs
    some (env.set slot (some value), memory, ⟨instruction.weight, {}⟩)
  | .call function args slot =>
    let (values, env) ← operands memory args env
    let (value, memory, cost) ← call function values memory
    some (env.set slot (some value), memory, (⟨instruction.weight, {}⟩ : Cost).plus cost)
  | .dropMoved slot =>
    match env slot with
    | none => some (env, memory, ⟨instruction.weight, {}⟩)
    | some _ => none

def actionBorrows : Action → Bool
  | .assign _ rhs => heapBorrows rhs
  | _ => true

def codeBorrows : Code → Bool
  | .done | .ret => true
  | .step instruction rest => actionBorrows instruction && codeBorrows rest
  | .branch _ _ _ yes no rest => codeBorrows yes && codeBorrows no && codeBorrows rest

inductive Result where
  | next : Locals → Result
  | returned : Cell → Result

def exec (call : Calls) : Code → Memory → Locals → Option (Result × Memory × Cost)
  | .done, memory, env => some (.next env, memory, {})
  | .ret, memory, env => do some (.returned (← env 0), memory, ⟨1, {}⟩)
  | .step instruction rest, memory, env => do
    let (env, memory, first) ← action call memory env instruction
    let (result, memory, last) ← exec call rest memory env
    some (result, memory, first.plus last)
  | .branch scrut key other yes no rest, memory, env => do
    let (actual, env) ← scrutinee memory env scrut
    let (result, memory, first) ← selectBranch actual key other
      (fun _ => exec call yes memory env) (fun _ => exec call no memory env)
    let charged := (⟨1 + scrut.weight, {}⟩ : Cost).plus first
    match result with
    | .returned value => some (.returned value, memory, charged)
    | .next env =>
      let (result, memory, last) ← exec call rest memory env
      some (result, memory, charged.plus last)

def initialLocals (args : List Cell) : Locals :=
  fun index => if index = 0 then none else args[index - 1]?

def run (body : Function → Code) : Nat → Calls
  | 0, _, _, _ => none
  | fuel + 1, function, args, memory =>
    if function = .boxNew then
      match args with
      | [value] => some ((alloc memory value).1, (alloc memory value).2, ⟨1, entryEvents function⟩)
      | _ => none
    else do
      let (outcome, memory, cost) ← exec (run body fuel) (body function) memory (initialLocals args)
      match outcome with
      | .next _ => none
      | .returned value =>
        some (value, memory, (⟨1, entryEvents function⟩ : Cost).plus cost)

def OutcomeRep (memory : Memory) : Result → Outcome → Prop
  | .next concrete, .next abstract => EnvRep memory concrete abstract
  | .returned cell, .returned value => Represents memory cell value
  | _, _ => False

/-- Local callee simulation, discharged by fuel induction for the actual
interpreter. No whole-run budget or representation theorem is assumed. -/
def CallsRefine (concrete : Calls) (abstract : Callees) : Prop :=
  ∀ function memory cells values value cost,
    RepresentsFields memory cells values → abstract function values = some (value, cost) →
    ∃ cell after, concrete function cells memory = some (cell, after, cost) ∧
      Represents after cell value ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations

theorem action_spec {call : Calls} {abstractCall : Callees}
    (hc : CallsRefine call abstractCall) {memory : Memory} {concrete : Locals} {abstract : Env}
    (he : EnvRep memory concrete abstract) (instruction : Action)
    (hb : actionBorrows instruction = true) {next : Env} {cost : Cost}
    (hr : evalAction abstractCall abstract instruction = some (next, cost)) :
    ∃ state after, action call memory concrete instruction = some (state, after, cost) ∧
      EnvRep after state next ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  cases instruction with
  | scope slot =>
    cases hr
    exact ⟨concrete.set slot none, memory, rfl, he.set slot .none, .refl memory, by rfl⟩
  | assign slot rhs =>
    simp only [evalAction] at hr
    cases hs : evalRValue abstract rhs with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨value, state⟩
      simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨cell, env, hrhs, hv, he'⟩ := rvalue_spec he rhs hb hs
      exact ⟨env.set slot (some cell), memory, by simp [action, hrhs],
        he'.set slot (.some hv), .refl memory, by rfl⟩
  | dropMoved slot =>
    simp only [evalAction] at hr
    cases hs : abstract slot with
    | some v => simp [hs] at hr
    | none =>
      simp only [hs, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      have hx := he slot
      rw [hs] at hx
      have hn : concrete slot = none := by
        cases hn : concrete slot with
        | none => rfl
        | some cell => rw [hn] at hx; cases hx
      exact ⟨concrete, memory, by simp [action, hn], he, .refl memory, by rfl⟩
  | call function args slot =>
    simp only [evalAction] at hr
    cases hs : evalOperands args abstract with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨values, state⟩
      cases hrCall : abstractCall function values with
      | none => simp [hs, hrCall] at hr
      | some pair =>
        rcases pair with ⟨value, inner⟩
        simp only [hs, hrCall, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨cells, env, hargs, hvalues, he'⟩ := operands_spec he args hs
        obtain ⟨cell, after, hrun, hv, hext, hlen⟩ := hc function memory cells values value inner hvalues hrCall
        exact ⟨env.set slot (some cell), after, by simp [action, hargs, hrun],
          (he'.mono hext).set slot (.some hv), hext,
          by simpa [Cost.plus, LookupEvents.Events.plus] using hlen⟩

theorem exec_spec {call : Calls} {abstractCall : Callees}
    (hc : CallsRefine call abstractCall) (code : Code) (hb : codeBorrows code = true)
    {memory : Memory} {concrete : Locals} {abstract : Env} (he : EnvRep memory concrete abstract)
    {outcome : Outcome} {cost : Cost} (hr : LookupSource.exec abstractCall code abstract = some (outcome, cost)) :
    ∃ result after, exec call code memory concrete = some (result, after, cost) ∧
      OutcomeRep after result outcome ∧ Extends memory after ∧
      after.length = memory.length + cost.events.allocations := by
  induction code generalizing memory concrete abstract outcome cost with
  | done =>
    cases hr
    exact ⟨.next concrete, memory, rfl, he, .refl memory, by rfl⟩
  | ret =>
    simp only [LookupSource.exec] at hr
    cases hs : abstract 0 with
    | none => simp [hs] at hr
    | some value =>
      simp only [hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl⟩ := hr
      obtain ⟨cell, hc, hv⟩ := he.get hs
      exact ⟨.returned cell, memory, by simp [exec, hc], hv, .refl memory, by rfl⟩
  | step instruction rest ih =>
    have hb' := Bool.and_eq_true_iff.mp hb
    simp only [LookupSource.exec] at hr
    cases ha : evalAction abstractCall abstract instruction with
    | none => simp [ha] at hr
    | some pair =>
      rcases pair with ⟨state, first⟩
      cases hs : LookupSource.exec abstractCall rest state with
      | none => simp [ha, hs] at hr
      | some pair =>
        rcases pair with ⟨last, second⟩
        simp only [ha, hs, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl⟩ := hr
        obtain ⟨middle, mem, ha', he', hex₁, hlen₁⟩ := action_spec hc he instruction hb'.1 ha
        obtain ⟨result, after, hs', ho, hex₂, hlen₂⟩ := ih hb'.2 he' hs
        refine ⟨result, after, by simp [exec, ha', hs'], ho, hex₁.trans hex₂, ?_⟩
        simp only [Cost.plus, LookupEvents.Events.plus] at *
        omega
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    have hb' := Bool.and_eq_true_iff.mp hb
    have hb'' := Bool.and_eq_true_iff.mp hb'.1
    simp only [LookupSource.exec] at hr
    cases hs : evalScrutinee abstract scrut with
    | none => simp [hs] at hr
    | some pair =>
      rcases pair with ⟨actual, state⟩
      cases hbranch : selectBranch actual key other
          (fun _ => LookupSource.exec abstractCall yes state)
          (fun _ => LookupSource.exec abstractCall no state) with
      | none => simp [hs, hbranch] at hr
      | some pair =>
        rcases pair with ⟨selected, first⟩
        obtain ⟨middle, hs', he'⟩ := scrutinee_spec he scrut hs
        have selected_run : ∃ result after,
            selectBranch actual key other
              (fun _ => exec call yes memory middle) (fun _ => exec call no memory middle) =
                some (result, after, first) ∧
              OutcomeRep after result selected ∧ Extends memory after ∧
              after.length = memory.length + first.events.allocations := by
          by_cases hy : actual = key
          · simpa only [selectBranch, hy, ite_true] using
              ihYes hb''.1 he' (by simpa only [selectBranch, hy, ite_true] using hbranch)
          · by_cases hn : other.all (· = actual) = true
            · simpa only [selectBranch, hy, ite_false, hn, ite_true] using
                ihNo hb''.2 he' (by simpa only [selectBranch, hy, ite_false, hn,
                  ite_true] using hbranch)
            · simp [selectBranch, hy, hn] at hbranch
        obtain ⟨result, mem, hr', ho, hex₁, hlen₁⟩ := selected_run
        cases selected with
        | returned value =>
          simp only [hs, hbranch, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          cases result with
          | next _ => cases ho
          | returned cell =>
            exact ⟨.returned cell, mem, by simp [exec, hs', hr'], ho, hex₁,
              by simpa [Cost.plus, LookupEvents.Events.plus] using hlen₁⟩
        | next state =>
          cases result with
          | returned _ => cases ho
          | next env =>
            simp only [hs, hbranch, bind, Option.bind] at hr
            cases ht : LookupSource.exec abstractCall rest state with
            | none => simp [ht] at hr
            | some pair =>
              rcases pair with ⟨last, second⟩
              simp only [ht, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl⟩ := hr
              obtain ⟨result, after, ht', ho', hex₂, hlen₂⟩ := ihRest hb'.2 ho ht
              refine ⟨result, after, by simp [exec, hs', hr', ht'], ho', hex₁.trans hex₂, ?_⟩
              simp only [Cost.plus, LookupEvents.Events.plus] at *
              omega

theorem initial_rep {memory : Memory} {cells : List Cell} {values : List Value}
    (h : RepresentsFields memory cells values) :
    EnvRep memory (initialLocals cells) (initialEnv values) := by
  intro index
  by_cases hi : index = 0
  · simp only [initialLocals, initialEnv, hi, ite_true]
    exact .none
  · simp only [initialLocals, initialEnv, hi, ite_false]
    exact h.get (index - 1)

theorem run_spec (body : Function → Code) (hb : ∀ function, codeBorrows (body function) = true)
    (fuel : Nat) : CallsRefine (run body fuel) (LookupSource.run body fuel) := by
  induction fuel with
  | zero => intro function memory cells values value cost _ hr; cases hr
  | succ fuel ih =>
    intro function memory cells values value cost hargs hr
    rw [LookupSource.run_succ] at hr
    by_cases hf : function = .boxNew
    · subst function
      simp only [ite_true] at hr
      cases values with
      | nil => cases hr
      | cons head tail =>
        cases tail with
        | cons _ _ => cases hr
        | nil =>
          cases hr
          cases hargs with
          | cons hhead htail =>
            cases htail
            refine ⟨(alloc memory _).1, (alloc memory _).2, ?_, alloc_rep hhead,
              Extends.append memory [_], (alloc_fresh memory _).2.2⟩
            simp [run]
    · simp only [hf, ite_false] at hr
      cases hx : LookupSource.exec (LookupSource.run body fuel) (body function) (initialEnv values) with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨outcome, inner⟩
        simp only [hx, bind, Option.bind] at hr
        cases outcome with
        | next _ => cases hr
        | returned v =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl⟩ := hr
          obtain ⟨result, after, he, hv, hex, hlen⟩ :=
            exec_spec ih (body function) (hb function) (initial_rep hargs) hx
          cases result with
          | next _ => cases hv
          | returned cell =>
            refine ⟨cell, after, by simp [run, hf, he], hv, hex, ?_⟩
            have hz : (entryEvents function).allocations = 0 := by cases function <;> simp_all [entryEvents]
            simpa [Cost.plus, LookupEvents.Events.plus, hz] using hlen

end SubtreeProofs.Rust.LookupSource.Heap
