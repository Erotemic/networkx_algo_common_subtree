module

public import SubtreeProofs.Rust.LookupFramePrimitives

/-! Frame-safe traces of the existing heap interpreter. The certificates
record each concrete clobber and callee occurrence, plus cleanup at return;
they are not inferred from final ownership or final heap equality. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Frame

abbrev CallSafetyFor (F : Type) := F → List Cell → Memory → Cell → Memory → Cost → Prop

abbrev CallSafety := CallSafetyFor Function

def CallSoundWith {F : Type} (argsMatch : F → List Cell → Prop) (resultFlag : F → Bool)
    (call : CallsFor F) (good : CallSafetyFor F) : Prop :=
  ∀ function cells memory cell after cost, argsMatch function cells →
    call function cells memory = some (cell, after, cost) →
    Matches (resultFlag function) cell ∧ good function cells memory cell after cost

def ActionSafeWith {F : Type} (argsMatch : F → List Cell → Prop)
    (call : CallsFor F) (good : CallSafetyFor F) (memory : Memory) (env : Locals) : Action F → Prop
  | .scope slot => Disposable (env slot)
  | .assign slot rhs =>
    ∀ cell middle, rvalue memory env rhs = some (cell, middle) → Disposable (middle slot)
  | .call function args slot =>
    ∀ cells middle, operands memory args env = some (cells, middle) →
      Disposable (middle slot) ∧ argsMatch function cells ∧
      ∀ cell after cost, call function cells memory = some (cell, after, cost) →
        good function cells memory cell after cost
  | .dropMoved slot => env slot = none

theorem action_soundWith {F : Type} {profile : F → List Bool → Bool} {resultFlag : F → Bool}
    {argsMatch : F → List Cell → Prop} {call : CallsFor F} {good : CallSafetyFor F}
    (hprofile : ∀ function flags cells, FieldsMatch flags cells → profile function flags = true → argsMatch function cells)
    (hcall : CallSoundWith argsMatch resultFlag call good)
    {state next : State} {memory after : Memory} {env env' : Locals} {cost : Cost}
    (he : StateRep state env) (instruction : Action F)
    (hs : inferActionWith profile resultFlag state instruction = some next)
    (hr : action call memory env instruction = some (env', after, cost)) :
    StateRep next env' ∧ ActionSafeWith argsMatch call good memory env instruction := by
  cases instruction with
  | scope slot =>
    cases hr
    exact store_spec he .none hs
  | assign slot rhs =>
    simp only [inferActionWith] at hs
    cases hf : inferRValue state rhs with
    | none => simp [hf] at hs
    | some pair =>
      rcases pair with ⟨flag, middle⟩
      simp only [hf, bind, Option.bind] at hs
      have hguard : ActionSafeWith argsMatch call good memory env (.assign slot rhs) := by
        intro cell locals hc
        obtain ⟨hm, he'⟩ := rvalue_sound he rhs hf hc
        exact (store_spec he' (.some hm) hs).2
      simp only [action] at hr
      cases hc : rvalue memory env rhs with
      | none => simp [hc] at hr
      | some pair =>
        rcases pair with ⟨cell, locals⟩
        simp only [hc, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨hm, he'⟩ := rvalue_sound he rhs hf hc
        exact ⟨(store_spec he' (.some hm) hs).1, hguard⟩
  | call function args slot =>
    simp only [inferActionWith] at hs
    cases hf : inferOperands state args with
    | none => simp [hf] at hs
    | some pair =>
      rcases pair with ⟨flags, middle⟩
      simp only [hf, bind, Option.bind] at hs
      split at hs
      next hcheck =>
        have hguard : ActionSafeWith argsMatch call good memory env (.call function args slot) := by
          intro cells locals hc
          obtain ⟨hm, he'⟩ := operands_sound he args hf hc
          have ha := hprofile function flags cells hm hcheck
          have hd := store_disposable he' hs
          exact ⟨hd, ha, fun cell after cost hr => (hcall _ _ _ _ _ _ ha hr).2⟩
        simp only [action] at hr
        cases hc : operands memory args env with
        | none => simp [hc] at hr
        | some pair =>
          rcases pair with ⟨cells, locals⟩
          cases hrCall : call function cells memory with
          | none => simp [hc, hrCall] at hr
          | some pair =>
            rcases pair with ⟨cell, mem, inner⟩
            simp only [hc, hrCall, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨hm, he'⟩ := operands_sound he args hf hc
            have ho := (hcall _ _ _ _ _ _ (hprofile function flags cells hm hcheck) hrCall).1
            exact ⟨(store_spec he' (.some ho) hs).1, hguard⟩
      next => cases hs
  | dropMoved slot =>
    simp only [inferActionWith] at hs
    split at hs
    next hclear =>
      have hnone : lookup state slot = none := by
        have hh := (Bool.and_eq_true_iff.mp hclear).2
        simpa using hh
      have hn := he.empty hnone
      cases hs
      simp only [action, hn, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨he, hn⟩
    next => cases hs

inductive GuardedWith {F : Type} (argsMatch : F → List Cell → Prop) (call : CallsFor F) (good : CallSafetyFor F) :
    Code F → Memory → Locals → Result → Memory → Cost → Prop where
  | done (memory : Memory) (env : Locals) : GuardedWith argsMatch call good .done memory env (.next env) memory {}
  | ret {memory : Memory} {env : Locals} {cell : Cell} :
      env 0 = some cell → (∀ index, index ≠ 0 → Disposable (env index)) →
      GuardedWith argsMatch call good .ret memory env (.returned cell) memory ⟨1, {}⟩
  | step {instruction : Action F} {rest : Code F} {memory middle after : Memory}
      {env next : Locals} {result : Result} {first last : Cost} :
      action call memory env instruction = some (next, middle, first) →
      ActionSafeWith argsMatch call good memory env instruction →
      GuardedWith argsMatch call good rest middle next result after last →
      GuardedWith argsMatch call good (.step instruction rest) memory env result after (first.plus last)
  | branchReturned {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code F}
      {memory after : Memory} {env next : Locals} {actual : Key} {cell : Cell} {first : Cost} :
      scrutinee memory env scrut = some (actual, next) →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      GuardedWith argsMatch call good arm memory next (.returned cell) after first →
      GuardedWith argsMatch call good (.branch scrut key other yes no rest) memory env (.returned cell) after
        ((⟨1 + scrut.weight, {}⟩ : Cost).plus first)
  | branchNext {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code F}
      {memory middle after : Memory} {env next resume : Locals} {actual : Key} {result : Result} {first last : Cost} :
      scrutinee memory env scrut = some (actual, next) →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      GuardedWith argsMatch call good arm memory next (.next resume) middle first →
      GuardedWith argsMatch call good rest middle resume result after last →
      GuardedWith argsMatch call good (.branch scrut key other yes no rest) memory env result after
        (((⟨1 + scrut.weight, {}⟩ : Cost).plus first).plus last)

def Post (post : State → Bool) (output : Bool) : Result → Prop
  | .next env => ∃ state, post state = true ∧ StateRep state env
  | .returned cell => Matches output cell

theorem selected_exec {F : Type} {call : CallsFor F} {actual key : Key} {other : Option Key}
    {yes no arm : Code F} (hs : selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm)
    (memory : Memory) (env : Locals) :
    selectBranch actual key other (fun _ => Heap.exec call yes memory env) (fun _ => Heap.exec call no memory env) =
      Heap.exec call arm memory env := by
  by_cases hy : actual = key
  · simp only [selectBranch, hy, ite_true, Option.some.injEq] at hs
    subst arm
    simp [selectBranch, hy]
  · by_cases hn : other.all (· = actual) = true
    · simp only [selectBranch, hy, ite_false, hn, ite_true, Option.some.injEq] at hs
      subst arm
      simp [selectBranch, hy, hn]
    · simp [selectBranch, hy, hn] at hs

theorem GuardedWith.erases {F : Type} {argsMatch : F → List Cell → Prop}
    {call : CallsFor F} {good : CallSafetyFor F} {code : Code F}
    {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : GuardedWith argsMatch call good code memory env result after cost) :
    Heap.exec call code memory env = some (result, after, cost) := by
  induction h with
  | done => rfl
  | ret hr _ => simp [Heap.exec, hr]
  | step ha _ _ ih => simp [Heap.exec, ha, ih]
  | branchReturned hs hsel _ ih => simp [Heap.exec, hs, selected_exec hsel, ih]
  | branchNext hs hsel _ _ ih₁ ih₂ => simp [Heap.exec, hs, selected_exec hsel, ih₁, ih₂]

theorem verify_soundWith {F : Type} {profile : F → List Bool → Bool} {resultFlag : F → Bool}
    {argsMatch : F → List Cell → Prop} {call : CallsFor F} {good : CallSafetyFor F}
    (hprofile : ∀ function flags cells, FieldsMatch flags cells → profile function flags = true → argsMatch function cells)
    (hcall : CallSoundWith argsMatch resultFlag call good) (code : Code F) {state : State} (post : State → Bool) (output : Bool)
    (hc : verifyWith profile resultFlag code state output post = true) {memory after : Memory} {env : Locals}
    (he : StateRep state env) {result : Result} {cost : Cost}
    (hr : Heap.exec call code memory env = some (result, after, cost)) :
    GuardedWith argsMatch call good code memory env result after cost ∧ Post post output result := by
  induction code generalizing state post output memory after env result cost with
  | done =>
    cases hr
    exact ⟨.done memory env, state, hc, he⟩
  | ret =>
    simp only [Heap.exec] at hr
    cases hx : env 0 with
    | none => simp [hx] at hr
    | some cell =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨hm, hframe⟩ := return_spec he hc hx
      exact ⟨.ret hx hframe, hm⟩
  | step instruction rest ih =>
    simp only [verifyWith] at hc
    cases hs : inferActionWith profile resultFlag state instruction with
    | none => simp [hs] at hc
    | some next =>
      simp only [hs] at hc
      simp only [Heap.exec] at hr
      cases ha : action call memory env instruction with
      | none => simp [ha] at hr
      | some pair =>
        rcases pair with ⟨locals, mem, first⟩
        cases ht : Heap.exec call rest mem locals with
        | none => simp [ha, ht] at hr
        | some pair =>
          rcases pair with ⟨lastResult, lastMemory, last⟩
          simp only [ha, ht, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          obtain ⟨he', hg⟩ := action_soundWith hprofile hcall he instruction hs ha
          obtain ⟨hg', hp⟩ := ih post output hc he' ht
          exact ⟨.step ha hg hg', hp⟩
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    simp only [verifyWith] at hc
    cases hst : inferScrutinee state scrut with
    | none => simp [hst] at hc
    | some next =>
      simp only [hst] at hc
      have hc' := Bool.and_eq_true_iff.mp hc
      simp only [Heap.exec] at hr
      cases hs : scrutinee memory env scrut with
      | none => simp [hs] at hr
      | some pair =>
        rcases pair with ⟨actual, locals⟩
        cases hb : selectBranch actual key other
            (fun _ => Heap.exec call yes memory locals) (fun _ => Heap.exec call no memory locals) with
        | none => simp [hs, hb] at hr
        | some pair =>
          rcases pair with ⟨selected, mem, first⟩
          have he' := scrutinee_sound he scrut hst hs
          have selected_safe : ∃ arm,
              selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm ∧
              GuardedWith argsMatch call good arm memory locals selected mem first ∧
              Post (fun s => verifyWith profile resultFlag rest s output post) output selected := by
            by_cases hy : actual = key
            · have hrYes : Heap.exec call yes memory locals = some (selected, mem, first) := by
                simpa only [selectBranch, hy, ite_true] using hb
              obtain ⟨hg, hp⟩ := ihYes (fun s => verifyWith profile resultFlag rest s output post) output hc'.1 he' hrYes
              exact ⟨yes, by simp [selectBranch, hy], hg, hp⟩
            · by_cases hn : other.all (· = actual) = true
              · have hrNo : Heap.exec call no memory locals = some (selected, mem, first) := by
                  simpa only [selectBranch, hy, ite_false, hn, ite_true] using hb
                obtain ⟨hg, hp⟩ := ihNo (fun s => verifyWith profile resultFlag rest s output post) output hc'.2 he' hrNo
                exact ⟨no, by simp [selectBranch, hy, hn], hg, hp⟩
              · simp [selectBranch, hy, hn] at hb
          obtain ⟨arm, hsel, hg, hp⟩ := selected_safe
          cases selected with
          | returned cell =>
            simp only [hs, hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨.branchReturned hs hsel hg, hp⟩
          | next resume =>
            obtain ⟨lastState, hcRest, heRest⟩ := hp
            simp only [hs, hb, bind, Option.bind] at hr
            cases ht : Heap.exec call rest mem resume with
            | none => simp [ht] at hr
            | some pair =>
              rcases pair with ⟨lastResult, lastMemory, last⟩
              simp only [ht, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              obtain ⟨hgRest, hpRest⟩ := ihRest post output hcRest heRest ht
              exact ⟨.branchNext hs hsel hg hgRest, hpRest⟩

abbrev CallSound (call : Calls) (good : CallSafety) : Prop := CallSoundWith ArgsMatch outputFlag call good
abbrev ActionSafe (call : Calls) (good : CallSafety) := ActionSafeWith ArgsMatch call good
abbrev Guarded (call : Calls) (good : CallSafety) := GuardedWith ArgsMatch call good

theorem action_sound {call : Calls} {good : CallSafety} (hcall : CallSound call good)
    {state next : State} {memory after : Memory} {env env' : Locals} {cost : Cost}
    (he : StateRep state env) (instruction : Action) (hs : inferAction state instruction = some next)
    (hr : action call memory env instruction = some (env', after, cost)) :
    StateRep next env' ∧ ActionSafe call good memory env instruction :=
  action_soundWith (profile := callProfile) (resultFlag := outputFlag) (argsMatch := ArgsMatch)
    (fun function _ _ hm hc => profile_sound (function := function) hm hc) hcall he instruction hs hr

theorem Guarded.erases {call : Calls} {good : CallSafety} {code : Code}
    {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : Guarded call good code memory env result after cost) :
    Heap.exec call code memory env = some (result, after, cost) := GuardedWith.erases h

theorem verify_sound {call : Calls} {good : CallSafety} (hcall : CallSound call good)
    (code : Code) {state : State} (post : State → Bool) (output : Bool)
    (hc : verify code state output post = true) {memory after : Memory} {env : Locals}
    (he : StateRep state env) {result : Result} {cost : Cost}
    (hr : Heap.exec call code memory env = some (result, after, cost)) :
    Guarded call good code memory env result after cost ∧ Post post output result :=
  verify_soundWith (profile := callProfile) (resultFlag := outputFlag) (argsMatch := ArgsMatch)
    (fun function _ _ hm hc => profile_sound (function := function) hm hc) hcall code post output hc he hr

end SubtreeProofs.Rust.LookupSource.Heap.Frame
