module

public import SubtreeProofs.Rust.LookupBorrowPrimitives
public import SubtreeProofs.Rust.LookupFrameExecution

/-! Intermediate typed-loan traces. Every stored/temporary shared reference
has a typed read in the retained caller heap. All normal control and costs
erase to the existing interpreter; callee contracts are discharged separately. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Borrow

def CallsSafe (base : Memory) (call : Calls) (good : Frame.CallSafety) : Prop :=
  ∀ function cells types memory cell after cost ty,
    Extends base memory → FieldsSafe base memory cells types → SourceTypes.callOutput function types = some ty →
    call function cells memory = some (cell, after, cost) →
    Safe base after cell ty ∧ Extends memory after ∧ good function cells memory cell after cost

def ActionWitness (base : Memory) (call : Calls) (good : Frame.CallSafety) (locals : List Ty)
    (memory : Memory) (env : Locals) : Action → Prop
  | .scope _ | .dropMoved _ => True
  | .assign _ rhs => ∀ cell middle, rvalue memory env rhs = some (cell, middle) →
      ∃ ty, SourceTypes.inferRValue locals rhs = some ty ∧ Safe base memory cell ty ∧ EnvSafe base memory locals middle
  | .call function args _ => ∀ cells middle, operands memory args env = some (cells, middle) →
      ∃ types, SourceTypes.inferOperands locals args = some types ∧ FieldsSafe base memory cells types ∧
        EnvSafe base memory locals middle ∧
        ∀ cell after cost, call function cells memory = some (cell, after, cost) →
          good function cells memory cell after cost

theorem action_safe {base : Memory} {call : Calls} {good : Frame.CallSafety} (hcall : CallsSafe base call good)
    {memory after : Memory} {locals : List Ty} {env env' : Locals} {cost : Cost}
    (hext : Extends base memory) (he : EnvSafe base memory locals env) (instruction : Action)
    (ht : SourceTypes.ActionConstraints locals instruction) (hroutes : actionRoutes locals instruction = true)
    (hr : action call memory env instruction = some (env', after, cost)) :
    EnvSafe base after locals env' ∧ Extends memory after ∧ ActionWitness base call good locals memory env instruction := by
  cases instruction with
  | scope slot => cases hr; exact ⟨he.clear slot, .refl memory, trivial⟩
  | dropMoved slot =>
    simp only [action] at hr
    cases hn : env slot with
    | some _ => simp [hn] at hr
    | none =>
      simp only [hn, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨he, .refl memory, trivial⟩
  | assign slot rhs =>
    obtain ⟨ty, hs, hd⟩ := ht
    have hw : ActionWitness base call good locals memory env (.assign slot rhs) := by
      intro cell middle hx
      obtain ⟨hv, he'⟩ := rvalue_safe hext he rhs hs hroutes hx
      exact ⟨ty, hs, hv, he'⟩
    simp only [action] at hr
    cases hx : rvalue memory env rhs with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨value, next⟩
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      obtain ⟨hv, he'⟩ := rvalue_safe hext he rhs hs hroutes hx
      exact ⟨he'.store hd hv, .refl memory, hw⟩
  | call function args slot =>
    obtain ⟨types, ty, hs, hc, hd⟩ := ht
    have hw : ActionWitness base call good locals memory env (.call function args slot) := by
      intro cells middle hx
      obtain ⟨hvs, he'⟩ := operands_safe hext he args hs hx
      exact ⟨types, hs, hvs, he', fun cell after cost hr =>
        (hcall _ _ _ _ _ _ _ _ hext hvs hc hr).2.2⟩
    simp only [action] at hr
    cases hx : operands memory args env with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨values, next⟩
      cases hy : call function values memory with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨value, mem, inner⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨hvs, he'⟩ := operands_safe hext he args hs hx
        obtain ⟨hv, hex, _⟩ := hcall _ _ _ _ _ _ _ _ hext hvs hc hy
        exact ⟨(he'.mono hex).store hd hv, hex, hw⟩

inductive Trace (base : Memory) (call : Calls) (good : Frame.CallSafety) (locals : List Ty) (output : Ty) :
    LookupSource.Code → Memory → Locals → Result → Memory → Cost → Prop where
  | done {memory : Memory} {env : Locals} : Extends base memory → EnvSafe base memory locals env →
      Trace base call good locals output .done memory env (.next env) memory {}
  | ret {memory : Memory} {env : Locals} {cell : Cell} :
      Extends base memory → EnvSafe base memory locals env → env 0 = some cell → Safe base memory cell output →
      Trace base call good locals output .ret memory env (.returned cell) memory ⟨1, {}⟩
  | step {instruction : Action} {rest : LookupSource.Code} {memory middle after : Memory}
      {env next : Locals} {result : Result} {first last : Cost} :
      Extends base memory → EnvSafe base memory locals env →
      action call memory env instruction = some (next, middle, first) →
      ActionWitness base call good locals memory env instruction →
      Trace base call good locals output rest middle next result after last →
      Trace base call good locals output (.step instruction rest) memory env result after (first.plus last)
  | branchReturned {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : LookupSource.Code}
      {memory after : Memory} {env next : Locals} {actual : Key} {cell : Cell} {first : Cost} :
      Extends base memory → EnvSafe base memory locals env →
      scrutinee memory env scrut = some (actual, next) → EnvSafe base memory locals next →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace base call good locals output arm memory next (.returned cell) after first →
      Trace base call good locals output (.branch scrut key other yes no rest) memory env (.returned cell) after
        ((⟨1 + scrut.weight, {}⟩ : Cost).plus first)
  | branchNext {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : LookupSource.Code}
      {memory middle after : Memory} {env next resume : Locals} {actual : Key} {result : Result} {first last : Cost} :
      Extends base memory → EnvSafe base memory locals env →
      scrutinee memory env scrut = some (actual, next) → EnvSafe base memory locals next →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace base call good locals output arm memory next (.next resume) middle first →
      Trace base call good locals output rest middle resume result after last →
      Trace base call good locals output (.branch scrut key other yes no rest) memory env result after
        (((⟨1 + scrut.weight, {}⟩ : Cost).plus first).plus last)

theorem Trace.erases {base : Memory} {call : Calls} {good : Frame.CallSafety} {locals : List Ty} {output : Ty}
    {code : LookupSource.Code} {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : Trace base call good locals output code memory env result after cost) :
    Heap.exec call code memory env = some (result, after, cost) := by
  induction h with
  | done => rfl
  | ret _ _ hr _ => simp [Heap.exec, hr]
  | step _ _ ha _ _ ih => simp [Heap.exec, ha, ih]
  | branchReturned _ _ hs _ hsel _ ih => simp [Heap.exec, hs, Frame.selected_exec hsel, ih]
  | branchNext _ _ hs _ hsel _ _ ih₁ ih₂ => simp [Heap.exec, hs, Frame.selected_exec hsel, ih₁, ih₂]

def Post (base current : Memory) (locals : List Ty) (output : Ty) : Result → Prop
  | .next env => EnvSafe base current locals env
  | .returned cell => Safe base current cell output

theorem exec_safe {base : Memory} {call : Calls} {good : Frame.CallSafety} (hcall : CallsSafe base call good)
    (code : LookupSource.Code) {memory after : Memory} {locals : List Ty} {output : Ty} {env : Locals}
    {result : Result} {cost : Cost} (hext : Extends base memory) (he : EnvSafe base memory locals env)
    (ht : SourceTypes.CodeConstraints locals output code) (hroutes : codeRoutes locals code = true)
    (hr : Heap.exec call code memory env = some (result, after, cost)) :
    Trace base call good locals output code memory env result after cost ∧
      Post base after locals output result ∧ Extends memory after := by
  induction ht generalizing memory after env result cost with
  | done => cases hr; exact ⟨.done hext he, he, .refl memory⟩
  | ret hret =>
    simp only [Heap.exec] at hr
    cases hx : env 0 with
    | none => simp [hx] at hr
    | some cell =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      have hv := he.get hx hret
      exact ⟨.ret hext he hx hv, hv, .refl memory⟩
  | @step instruction rest ha ht ih =>
    have hroute := Bool.and_eq_true_iff.mp hroutes
    simp only [Heap.exec] at hr
    cases hx : action call memory env instruction with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨next, mem, first⟩
      cases hy : Heap.exec call rest mem next with
      | none => simp [hx, hy] at hr
      | some pair =>
        rcases pair with ⟨lastResult, lastMemory, last⟩
        simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        obtain ⟨he', hex, hw⟩ := action_safe hcall hext he instruction ha hroute.1 hx
        obtain ⟨trace, hp, hex'⟩ := ih (hext.trans hex) he' hroute.2 hy
        exact ⟨.step hext he hx hw trace, hp, hex.trans hex'⟩
  | @branch scrut key other yes no rest kind hs hk ho hy hn ht ihYes ihNo ihRest =>
    have hroute := Bool.and_eq_true_iff.mp hroutes
    have hroute' := Bool.and_eq_true_iff.mp hroute.1
    simp only [Heap.exec] at hr
    cases hx : scrutinee memory env scrut with
    | none => simp [hx] at hr
    | some pair =>
      rcases pair with ⟨actual, next⟩
      cases hb : selectBranch actual key other
          (fun _ => Heap.exec call yes memory next) (fun _ => Heap.exec call no memory next) with
      | none => simp [hx, hb] at hr
      | some pair =>
        rcases pair with ⟨selected, mem, first⟩
        have he' := scrutinee_safe hext he scrut hs hx
        have hselected : ∃ arm,
            selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm ∧
            Trace base call good locals output arm memory next selected mem first ∧
            Post base mem locals output selected ∧ Extends memory mem := by
          by_cases ha : actual = key
          · obtain ⟨trace, hp, hex⟩ := ihYes hext he' hroute'.1 (by simpa only [selectBranch, ha, ite_true] using hb)
            exact ⟨yes, by simp [selectBranch, ha], trace, hp, hex⟩
          · by_cases ha' : other.all (· = actual) = true
            · obtain ⟨trace, hp, hex⟩ := ihNo hext he' hroute'.2
                (by simpa only [selectBranch, ha, ite_false, ha', ite_true] using hb)
              exact ⟨no, by simp [selectBranch, ha, ha'], trace, hp, hex⟩
            · simp [selectBranch, ha, ha'] at hb
        obtain ⟨arm, hsel, trace, hp, hex⟩ := hselected
        cases selected with
        | returned cell =>
          simp only [hx, hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          exact ⟨.branchReturned hext he hx he' hsel trace, hp, hex⟩
        | next resume =>
          simp only [hx, hb, bind, Option.bind] at hr
          cases hz : Heap.exec call rest mem resume with
          | none => simp [hz] at hr
          | some pair =>
            rcases pair with ⟨lastResult, lastMemory, last⟩
            simp only [hz, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            obtain ⟨trace', hp', hex'⟩ := ihRest (hext.trans hex) hp hroute.2 hz
            exact ⟨.branchNext hext he hx he' hsel trace trace', hp', hex.trans hex'⟩

end SubtreeProofs.Rust.LookupSource.Heap.Borrow
