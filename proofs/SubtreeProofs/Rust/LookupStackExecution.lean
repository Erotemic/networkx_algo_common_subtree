module

public import SubtreeProofs.Rust.LookupStackPrimitives
public import SubtreeProofs.Rust.LookupFrameExecution

/-! Source storage traces with distinct allocation/deallocation and actual
value environments. Callee occurrences retain their own stack certificates.
Erasure preserves the unchanged successful heap run and its complete cost. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Stack

open Heap

abbrev CallSafety := Frame.CallSafety

def CallSound (call : Calls) (good : CallSafety) : Prop :=
  ∀ function cells memory cell after cost, cells.length = Frontend.arity function →
    call function cells memory = some (cell, after, cost) → good function cells memory cell after cost

def ActionSafe (call : Calls) (good : CallSafety) (state : State) (memory : Memory) (env : Locals) : Control.Action → Prop
  | .storageLive slot | .storageDead slot => slot < state.length
  | .assign slot rhs => ∀ cell middle, rvalue memory env rhs = some (cell, middle) →
      ∃ next, inferRValue state rhs = some next ∧ StateRep next middle ∧ status next slot ≠ .dead
  | .call function args slot => ∀ cells middle, operands memory args env = some (cells, middle) →
      ∃ next, inferOperands state args = some next ∧ StateRep next middle ∧ status next slot ≠ .dead ∧
        cells.length = Frontend.arity function ∧
        ∀ cell after cost, call function cells memory = some (cell, after, cost) →
          good function cells memory cell after cost
  | .dropConditional slot => status state slot = .empty

theorem action_sound {call : Calls} {good : CallSafety} (hcall : CallSound call good)
    {state next : State} {memory after : Memory} {env env' : Locals} {cost : Cost}
    (he : StateRep state env) (instruction : Control.Action)
    (hs : inferAction state instruction = some next)
    (hr : action call memory env instruction.lower = some (env', after, cost)) :
    StateRep next env' ∧ ActionSafe call good state memory env instruction := by
  cases instruction with
  | storageLive slot =>
    simp only [inferAction] at hs
    split at hs
    next hb =>
      cases hs
      cases hr
      exact ⟨he.set slot hb trivial, hb⟩
    next => cases hs
  | storageDead slot =>
    simp only [inferAction] at hs
    split at hs
    next hb =>
      cases hs
      cases hr
      exact ⟨he.set slot hb trivial, hb⟩
    next => cases hs
  | assign slot rhs =>
    simp only [inferAction] at hs
    cases hf : inferRValue state rhs with
    | none => simp [hf] at hs
    | some middle =>
      simp only [hf, bind, Option.bind] at hs
      have hw : ActionSafe call good state memory env (.assign slot rhs) := by
        intro cell locals hc
        have he' := rvalue_sound he rhs hf hc
        exact ⟨middle, hf, he', (store_spec he' hs cell).2⟩
      simp only [Control.Action.lower, action] at hr
      cases hx : rvalue memory env rhs with
      | none => simp [hx] at hr
      | some pair =>
        rcases pair with ⟨cell, locals⟩
        simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        exact ⟨(store_spec (rvalue_sound he rhs hf hx) hs cell).1, hw⟩
  | call function args slot =>
    simp only [inferAction] at hs
    split at hs
    next harity =>
      have harity : args.length = Frontend.arity function := by simpa using harity
      cases hf : inferOperands state args with
      | none => simp [hf] at hs
      | some middle =>
        simp only [hf, bind, Option.bind] at hs
        have hw : ActionSafe call good state memory env (.call function args slot) := by
          intro cells locals hc
          have he' := operands_sound he args hf hc
          have hlen := (operands_length args hc).trans harity
          exact ⟨middle, hf, he', (store_spec he' hs (.boolean false)).2, hlen,
            fun cell after cost hr => hcall _ _ _ _ _ _ hlen hr⟩
        simp only [Control.Action.lower, action] at hr
        cases hx : operands memory args env with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨cells, locals⟩
          cases hy : call function cells memory with
          | none => simp [hx, hy] at hr
          | some pair =>
            rcases pair with ⟨cell, mem, inner⟩
            simp only [hx, hy, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨(store_spec (operands_sound he args hf hx) hs cell).1, hw⟩
    next => cases hs
  | dropConditional slot =>
    simp only [inferAction] at hs
    split at hs
    next hb =>
      have hslot : status state slot = .empty := by simpa using (Bool.and_eq_true_iff.mp hb).2
      have hn : env slot = none := he.empty (by simp [hslot])
      cases hs
      simp only [Control.Action.lower, action, hn, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨he, hslot⟩
    next => cases hs

def close (state : State) : State := List.replicate state.length .dead

theorem closed_frame (state : State) : StateRep (close state) (fun _ => none) := by
  intro index
  simp only [close, status, List.getElem?_replicate]
  split <;> trivial

inductive Trace (call : Calls) (good : CallSafety) :
    Code → State → Memory → Locals → Result → Memory → Cost → Prop where
  | done {state : State} {memory : Memory} {env : Locals} : StateRep state env →
      Trace call good .done state memory env (.next env) memory {}
  | ret {state : State} {memory : Memory} {env : Locals} {cell : Cell} :
      StateRep state env → status state 0 = .full → env 0 = some cell →
      StateRep (close state) (fun _ => none) →
      Trace call good .ret state memory env (.returned cell) memory ⟨1, {}⟩
  | step {instruction : Control.Action} {rest : Code} {state next : State}
      {memory middle after : Memory} {env locals : Locals} {result : Result} {first last : Cost} :
      StateRep state env → inferAction state instruction = some next →
      action call memory env instruction.lower = some (locals, middle, first) →
      ActionSafe call good state memory env instruction →
      Trace call good rest next middle locals result after last →
      Trace call good (.step instruction rest) state memory env result after (first.plus last)
  | branchReturned {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code}
      {state next : State} {memory after : Memory} {env locals : Locals}
      {actual : Key} {cell : Cell} {first : Cost} :
      StateRep state env → inferScrutinee state scrut = some next →
      scrutinee memory env scrut = some (actual, locals) → StateRep next locals →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace call good arm next memory locals (.returned cell) after first →
      Trace call good (.branch scrut key other yes no rest) state memory env (.returned cell) after
        ((⟨1 + scrut.weight, {}⟩ : Cost).plus first)
  | branchNext {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest arm : Code}
      {state next resume : State} {memory middle after : Memory} {env locals final : Locals}
      {actual : Key} {result : Result} {first last : Cost} :
      StateRep state env → inferScrutinee state scrut = some next →
      scrutinee memory env scrut = some (actual, locals) → StateRep next locals →
      selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm →
      Trace call good arm next memory locals (.next final) middle first →
      StateRep resume final → Trace call good rest resume middle final result after last →
      Trace call good (.branch scrut key other yes no rest) state memory env result after
        (((⟨1 + scrut.weight, {}⟩ : Cost).plus first).plus last)

theorem selected_erase {actual key : Key} {other : Option Key} {yes no arm : Code}
    (hs : selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm) :
    selectBranch actual key other (fun _ => some yes.erase) (fun _ => some no.erase) = some arm.erase := by
  by_cases hy : actual = key
  · simp only [selectBranch, hy, ite_true, Option.some.injEq] at hs
    subst arm; simp [selectBranch, hy]
  · by_cases hn : other.all (· = actual) = true
    · simp only [selectBranch, hy, ite_false, hn, ite_true, Option.some.injEq] at hs
      subst arm; simp [selectBranch, hy, hn]
    · simp [selectBranch, hy, hn] at hs

theorem Trace.erases {call : Calls} {good : CallSafety} {code : Code} {state : State}
    {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : Trace call good code state memory env result after cost) :
    Heap.exec call code.erase memory env = some (result, after, cost) := by
  induction h with
  | done => rfl
  | ret _ _ hr _ => simp [Code.erase, Heap.exec, hr]
  | step _ _ ha _ _ ih => simp [Code.erase, Heap.exec, ha, ih]
  | branchReturned _ _ hs _ hsel _ ih =>
    simp [Code.erase, Heap.exec, hs, Frame.selected_exec (selected_erase hsel), ih]
  | branchNext _ _ hs _ hsel _ _ _ ih₁ ih₂ =>
    simp [Code.erase, Heap.exec, hs, Frame.selected_exec (selected_erase hsel), ih₁, ih₂]

def Post (post : State → Bool) : Result → Prop
  | .next env => ∃ state, post state = true ∧ StateRep state env
  | .returned _ => True

theorem verify_sound {call : Calls} {good : CallSafety} (hcall : CallSound call good)
    (code : Code) {state : State} (post : State → Bool) (hc : verify code state post = true)
    {memory after : Memory} {env : Locals} (he : StateRep state env) {result : Result} {cost : Cost}
    (hr : Heap.exec call code.erase memory env = some (result, after, cost)) :
    Trace call good code state memory env result after cost ∧ Post post result := by
  induction code generalizing state post memory after env result cost with
  | done => cases hr; exact ⟨.done he, state, hc, he⟩
  | ret =>
    have hfull : status state 0 = .full := by simpa [verify] using hc
    simp only [Code.erase, Heap.exec] at hr
    cases hx : env 0 with
    | none => simp [hx] at hr
    | some cell =>
      simp only [hx, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
      obtain ⟨rfl, rfl, rfl⟩ := hr
      exact ⟨.ret he hfull hx (closed_frame state), trivial⟩
  | step instruction rest ih =>
    simp only [verify] at hc
    cases hs : inferAction state instruction with
    | none => simp [hs] at hc
    | some next =>
      simp only [hs] at hc
      simp only [Code.erase, Heap.exec] at hr
      cases ha : action call memory env instruction.lower with
      | none => simp [ha] at hr
      | some pair =>
        rcases pair with ⟨locals, mem, first⟩
        cases ht : Heap.exec call rest.erase mem locals with
        | none => simp [ha, ht] at hr
        | some pair =>
          rcases pair with ⟨lastResult, lastMemory, last⟩
          simp only [ha, ht, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          obtain ⟨he', hw⟩ := action_sound hcall he instruction hs ha
          obtain ⟨trace, hp⟩ := ih post hc he' ht
          exact ⟨.step he hs ha hw trace, hp⟩
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    simp only [verify] at hc
    cases hst : inferScrutinee state scrut with
    | none => simp [hst] at hc
    | some next =>
      simp only [hst] at hc
      have hc' := Bool.and_eq_true_iff.mp hc
      simp only [Code.erase, Heap.exec] at hr
      cases hs : scrutinee memory env scrut with
      | none => simp [hs] at hr
      | some pair =>
        rcases pair with ⟨actual, locals⟩
        cases hb : selectBranch actual key other
            (fun _ => Heap.exec call yes.erase memory locals) (fun _ => Heap.exec call no.erase memory locals) with
        | none => simp [hs, hb] at hr
        | some pair =>
          rcases pair with ⟨selected, mem, first⟩
          have he' := scrutinee_sound he scrut hst hs
          have hselected : ∃ arm,
              selectBranch actual key other (fun _ => some yes) (fun _ => some no) = some arm ∧
              Trace call good arm next memory locals selected mem first ∧
              Post (fun state => verify rest state post) selected := by
            by_cases hy : actual = key
            · obtain ⟨trace, hp⟩ := ihYes (fun state => verify rest state post) hc'.1 he'
                (by simpa only [selectBranch, hy, ite_true] using hb)
              exact ⟨yes, by simp [selectBranch, hy], trace, hp⟩
            · by_cases hn : other.all (· = actual) = true
              · obtain ⟨trace, hp⟩ := ihNo (fun state => verify rest state post) hc'.2 he'
                  (by simpa only [selectBranch, hy, ite_false, hn, ite_true] using hb)
                exact ⟨no, by simp [selectBranch, hy, hn], trace, hp⟩
              · simp [selectBranch, hy, hn] at hb
          obtain ⟨arm, hsel, trace, hp⟩ := hselected
          cases selected with
          | returned cell =>
            simp only [hs, hb, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨.branchReturned he hst hs he' hsel trace, trivial⟩
          | next final =>
            obtain ⟨resume, hrest, heRest⟩ := hp
            simp only [hs, hb, bind, Option.bind] at hr
            cases ht : Heap.exec call rest.erase mem final with
            | none => simp [ht] at hr
            | some pair =>
              rcases pair with ⟨lastResult, lastMemory, last⟩
              simp only [ht, Option.some.injEq, Prod.mk.injEq] at hr
              obtain ⟨rfl, rfl, rfl⟩ := hr
              obtain ⟨trace', hp⟩ := ihRest post hrest heRest ht
              exact ⟨.branchNext he hst hs he' hsel trace heRest trace', hp⟩

end SubtreeProofs.Rust.LookupSource.Stack
