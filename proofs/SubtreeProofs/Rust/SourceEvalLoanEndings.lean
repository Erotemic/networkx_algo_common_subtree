module

public import SubtreeProofs.Rust.SourceEvalLoanObservations

/-! A reference view can end when the actual remaining code resets its local
before observing it, or returns without reading it. Complete source outcomes
and costs are invariant. This changes no independent source semantics. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.LoanEnding

open LookupSource LookupSource.Partial

def endsBeforeObservation (slot : Nat) : Code → Bool
  | .done => false
  | .ret => decide (slot ≠ 0)
  | .step act rest => avoidsAction slot act && (decide (writes act = some slot) || endsBeforeObservation slot rest)
  | .switch scrut _ _ left right _ => avoidsScrutinee slot scrut &&
      (endsBeforeObservation slot left && endsBeforeObservation slot right)

theorem exec_congr (call : Calls) (slot : Nat) (code : Code) (hn : endsBeforeObservation slot code = true)
    {first second : State} (hs : Same slot first second) : SourceEval.exec call code first = SourceEval.exec call code second := by
  induction code generalizing first second with
  | done => cases hn
  | ret =>
    have hzero := hs 0 (Ne.symm (of_decide_eq_true hn))
    simp only [SourceEval.exec_ret, SourceEval.returnValue, hzero]
  | step act rest ih =>
    have hparts := Bool.and_eq_true_iff.mp hn
    rw [SourceEval.exec_step, SourceEval.exec_step]
    apply rel_eq
    apply rel_bind (action_congr hs call act hparts.1)
    rintro ⟨middle, cost⟩ ⟨current, other⟩ ⟨hm, rfl, hw⟩
    dsimp only at hm hw ⊢
    have he : SourceEval.exec call rest middle = SourceEval.exec call rest current := by
      rcases Bool.or_eq_true_iff.mp hparts.2 with hwrite | hrest
      · rw [hw (of_decide_eq_true hwrite)]
      · exact ih hrest hm
    rw [he]
    exact rel_same _
  | switch scrut cases fallback left right rest ihLeft ihRight _ =>
    have hparts := Bool.and_eq_true_iff.mp hn
    have hbranches := Bool.and_eq_true_iff.mp hparts.2
    rw [Legacy.exec_switch, Legacy.exec_switch]
    apply rel_eq
    apply rel_bind (scrutinee_congr hs scrut hparts.1)
    rintro ⟨key, middle⟩ ⟨other, current⟩ ⟨rfl, hm⟩
    dsimp only at hm ⊢
    rw [ihLeft hbranches.1 hm, ihRight hbranches.2 hm]
    exact rel_same _

-- The data wrapper makes the finite scan finish before its function-valued
-- state is installed in an activation. Returning the function directly lets
-- compiler eta expansion repeat the entire scan on every later local read.
structure Prepared where
  state : State

def prepare (code : Code) : List Nat → State → Prepared
  | [], state => ⟨state⟩
  | slot :: rest, state =>
    match state slot with
    | .shared _ => prepare code rest (if endsBeforeObservation slot code then state.set slot .empty else state)
    | _ => prepare code rest state

def forget (code : Code) (slots : List Nat) (state : State) : State := (prepare code slots state).state

theorem forget_nil (code : Code) (state : State) : forget code [] state = state := rfl

theorem forget_cons (code : Code) (slot : Nat) (rest : List Nat) (state : State) :
    forget code (slot :: rest) state = (match state slot with
      | .shared _ => forget code rest (if endsBeforeObservation slot code then state.set slot .empty else state)
      | _ => forget code rest state) := by
  cases hs : state slot <;> simp only [forget, prepare, hs]

theorem forget_source (call : Calls) (code : Code) (slots : List Nat) (state : State) :
    SourceEval.exec call code (forget code slots state) = SourceEval.exec call code state := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    simp only [forget_cons]
    cases hs : state slot <;> try exact ih state
    rw [ih]
    by_cases he : endsBeforeObservation slot code = true
    · simp only [he, ite_true]
      exact (exec_congr call slot code he (Same.forget state slot)).symm
    · simp only [he, Bool.false_eq_true, ite_false]

theorem forget_boxes (code : Code) (slots : List Nat) (state : State) (index : Nat) :
    ((forget code slots state) index).dropWork.boxes = (state index).dropWork.boxes := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    simp only [forget_cons]
    cases hs : state slot <;> try exact ih state
    rw [ih]
    by_cases he : endsBeforeObservation slot code = true
    · simp only [he, ite_true]
      by_cases hi : index = slot
      · subst index
        simp only [Locals.set, ite_true, hs, Slot.dropWork]
      · simp only [Locals.set, hi, ite_false]
    · simp only [he, Bool.false_eq_true, ite_false]

theorem forget_observed (code : Code) (slots : List Nat) (state : State) (index : Nat)
    (hn : endsBeforeObservation index code = false) : (forget code slots state) index = state index := by
  induction slots generalizing state with
  | nil => rfl
  | cons slot rest ih =>
    simp only [forget_cons]
    cases hs : state slot <;> try exact ih state
    dsimp only
    rw [ih]
    by_cases he : endsBeforeObservation slot code = true
    · simp only [he, ite_true]
      have hi : index ≠ slot := by intro h; subst index; rw [hn] at he; cases he
      simp only [Locals.set, hi, ite_false]
    · simp only [he, Bool.false_eq_true, ite_false]

end SubtreeProofs.Rust.SourceEval.LoanEnding
