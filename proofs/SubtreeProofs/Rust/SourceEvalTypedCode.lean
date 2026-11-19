module

public import SubtreeProofs.Rust.SourceEvalTypes

/-! Static constraints for all retained control arms, including fake reads,
live drops and the explicit undefined-behavior leaf. The latter remains a
rejected execution, not a proof of reachability or memory safety. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap SourceTypes

def checkAction (locals : List Ty) : SourceEval.Action → Bool
  | .storageLive slot | .storageDead slot | .drop slot => slot < locals.length
  | .fakeRead place => (inferPlace locals place).isSome
  | .undefinedBehavior => true
  | .assign slot rhs => match locals[slot]? with
    | some ty => checkExpr locals ty rhs
    | none => false
  | .call function args slot => match inferOperands locals args with
    | some types => sameResult (callOutput function types) locals[slot]?
    | none => false

def ActionConstraints (locals : List Ty) : SourceEval.Action → Prop
  | .storageLive slot | .storageDead slot | .drop slot => slot < locals.length
  | .fakeRead place => ∃ ty, inferPlace locals place = some ty
  | .undefinedBehavior => True
  | .assign slot rhs => ∃ ty, locals[slot]? = some ty ∧ ExprConstraints locals rhs ty
  | .call function args slot => ∃ types ty,
      inferOperands locals args = some types ∧ callOutput function types = some ty ∧ locals[slot]? = some ty

theorem checkAction_sound {locals : List Ty} {instruction : SourceEval.Action}
    (h : checkAction locals instruction = true) : ActionConstraints locals instruction := by
  cases instruction with
  | storageLive slot | storageDead slot | drop slot => simpa [checkAction, ActionConstraints] using h
  | undefinedBehavior => trivial
  | fakeRead place => exact Option.isSome_iff_exists.mp h
  | assign slot rhs =>
    cases ht : locals[slot]? with
    | none => simp [checkAction, ht] at h
    | some ty => exact ⟨ty, ht, checkExpr_sound (by simpa only [checkAction, ht] using h)⟩
  | call function args slot =>
    cases ha : inferOperands locals args with
    | none => simp [checkAction, ha] at h
    | some types =>
      obtain ⟨ty, ho, hl⟩ := sameResult_sound (by simpa only [checkAction, ha] using h)
      exact ⟨types, ty, ha, ho, hl⟩

def discriminantKind : Ty → Option Kind
  | .adt kind => some kind
  | .tuple _ => some .tuple
  | .option _ => some .optional
  | _ => none

def scrutineeType (locals : List Ty) : Scrutinee → Option (Option Kind)
  | .value op => if sameResult (SourceTypes.inferOperand locals op) (some .boolean) then some none else none
  | .discriminant place => (discriminantKind <$> inferPlace locals place).join.map some

def checkCode (locals : List Ty) (result : Ty) : SourceEval.Code → Bool
  | .done => true
  | .ret => sameResult locals[0]? (some result)
  | .step instruction rest => checkAction locals instruction && checkCode locals result rest
  | .switch scrut branches _ yes no rest =>
    match scrutineeType locals scrut with
    | none => false
    | some kind => branches.all (fun branch => keyMatches kind branch.1) &&
        checkCode locals result yes && checkCode locals result no && checkCode locals result rest

inductive CodeConstraints (locals : List Ty) (result : Ty) : SourceEval.Code → Prop where
  | done : CodeConstraints locals result .done
  | ret : locals[0]? = some result → CodeConstraints locals result .ret
  | step {instruction : SourceEval.Action} {rest : SourceEval.Code} :
      ActionConstraints locals instruction → CodeConstraints locals result rest →
      CodeConstraints locals result (.step instruction rest)
  | switch {scrut : Scrutinee} {branches : List (Key × Nat)} {fallback : Option Nat}
      {yes no rest : SourceEval.Code} {kind : Option Kind} :
      scrutineeType locals scrut = some kind → branches.all (fun branch => keyMatches kind branch.1) = true →
      CodeConstraints locals result yes → CodeConstraints locals result no → CodeConstraints locals result rest →
      CodeConstraints locals result (.switch scrut branches fallback yes no rest)

theorem checkCode_sound {locals : List Ty} {result : Ty} {code : SourceEval.Code}
    (h : checkCode locals result code = true) : CodeConstraints locals result code := by
  induction code with
  | done => exact .done
  | ret =>
    obtain ⟨ty, hl, hr⟩ := sameResult_sound h
    cases hr
    exact .ret hl
  | step instruction rest ih =>
    have hh := Bool.and_eq_true_iff.mp h
    exact .step (checkAction_sound hh.1) (ih hh.2)
  | switch scrut branches fallback yes no rest ihYes ihNo ihRest =>
    cases hs : scrutineeType locals scrut with
    | none => simp [checkCode, hs] at h
    | some kind =>
      simp only [checkCode, hs, Bool.and_eq_true_iff] at h
      exact .switch hs h.1.1.1 (ihYes h.1.1.2) (ihNo h.1.2) (ihRest h.2)

end SubtreeProofs.Rust.SourceEval.Types
