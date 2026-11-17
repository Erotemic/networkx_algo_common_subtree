module

public import SubtreeProofs.Rust.LookupSourceTypes
public import SubtreeProofs.Rust.LookupSourceControl

/-! Static lifetime-erased type constraints for the normalized lookup syntax.
Initialization/ownership is checked separately by the frame analysis. This
module does not infer borrow regions or prove runtime type preservation. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

def inferPlace (locals : List Ty) : Place → Option Ty
  | .local slot => locals[slot]?
  | .deref parent => do deref (← inferPlace locals parent)
  | .field parent variant index => do fieldType (← inferPlace locals parent) variant index

def inferOperand (locals : List Ty) : Operand → Option Ty
  | .move slot => locals[slot]?
  | .boolean _ => some .boolean
  | .copy place => do
    let ty ← inferPlace locals place
    if copyable ty then some ty else none

def inferOperands (locals : List Ty) (args : List Operand) : Option (List Ty) := args.mapM (inferOperand locals)

def inferRValue (locals : List Ty) : RValue → Option Ty
  | .use op => inferOperand locals op
  | .address place => Ty.shared <$> inferPlace locals place
  | .aggregate kind variant args => do
    let types ← inferOperands locals args
    let result := if kind = .tuple then Ty.tuple types else .adt kind
    let expected ← constructorFields kind variant result
    if sameList types expected then some result else none

theorem aggregate_shape {locals : List Ty} {kind : Kind} {variant : Nat} {args : List Operand} {ty : Ty}
    (h : inferRValue locals (.aggregate kind variant args) = some ty) :
    ∃ fields, inferOperands locals args = some fields ∧ Shape kind variant fields ty := by
  simp only [inferRValue] at h
  cases ht : inferOperands locals args with
  | none => simp [ht] at h
  | some types =>
    cases hs : constructorFields kind variant (if kind = .tuple then .tuple types else .adt kind) with
    | none => simp [ht, hs] at h
    | some expected =>
      simp only [ht, hs, bind, Option.bind] at h
      split at h
      next he =>
        have heq := sameList_eq he
        rw [← heq] at hs
        cases h
        exact ⟨types, rfl, constructorFields_sound hs⟩
      next => cases h

def sameResult (actual : Option Ty) (expected : Option Ty) : Bool :=
  match actual, expected with
  | some actual, some expected => same actual expected
  | _, _ => false

theorem sameResult_sound {actual expected : Option Ty} (h : sameResult actual expected = true) :
    ∃ ty, actual = some ty ∧ expected = some ty := by
  cases actual <;> cases expected <;> simp only [sameResult] at h <;> try contradiction
  have he := same_eq h
  subst_vars
  exact ⟨_, rfl, rfl⟩

def checkAction (locals : List Ty) : Action → Bool
  | .scope slot | .dropMoved slot => slot < locals.length
  | .assign slot rhs => sameResult (inferRValue locals rhs) locals[slot]?
  | .call function args slot =>
    match inferOperands locals args with
    | none => false
    | some types => sameResult (callOutput function types) locals[slot]?

def scrutineeType (locals : List Ty) : Scrutinee → Option (Option Kind)
  | .value op => if sameResult (inferOperand locals op) (some .boolean) then some none else none
  | .discriminant place => do
    match ← inferPlace locals place with
    | .adt kind => some (some kind)
    | .tuple _ => some (some .tuple)
    | _ => none

def keyMatches : Option Kind → Key → Bool
  | none, .boolean _ => true
  | some kind, .variant actual variant =>
    kind == actual &&
      (if kind = .tuple then variant == 0 else (constructorFields kind variant (.adt kind)).isSome)
  | _, _ => false

def checkCode (locals : List Ty) (result : Ty) : Code → Bool
  | .done => true
  | .ret => sameResult locals[0]? (some result)
  | .step instruction rest => checkAction locals instruction && checkCode locals result rest
  | .branch scrut key other yes no rest =>
    match scrutineeType locals scrut with
    | none => false
    | some kind => keyMatches kind key && other.all (keyMatches kind) &&
        checkCode locals result yes && checkCode locals result no && checkCode locals result rest

def ActionConstraints (locals : List Ty) : Action → Prop
  | .scope slot | .dropMoved slot => slot < locals.length
  | .assign slot rhs => ∃ ty, inferRValue locals rhs = some ty ∧ locals[slot]? = some ty
  | .call function args slot => ∃ types ty,
      inferOperands locals args = some types ∧ callOutput function types = some ty ∧ locals[slot]? = some ty

theorem checkAction_sound {locals : List Ty} {instruction : Action} (h : checkAction locals instruction = true) :
    ActionConstraints locals instruction := by
  cases instruction with
  | scope slot => simpa [checkAction, ActionConstraints] using h
  | dropMoved slot => simpa [checkAction, ActionConstraints] using h
  | assign slot rhs => exact sameResult_sound h
  | call function args slot =>
    simp only [checkAction] at h
    cases ht : inferOperands locals args with
    | none => simp [ht] at h
    | some types =>
      obtain ⟨ty, ho, hs⟩ := sameResult_sound (by simpa only [ht] using h)
      exact ⟨types, ty, ht, ho, hs⟩

inductive CodeConstraints (locals : List Ty) (result : Ty) : Code → Prop where
  | done : CodeConstraints locals result .done
  | ret : locals[0]? = some result → CodeConstraints locals result .ret
  | step {instruction : Action} {rest : Code} :
      ActionConstraints locals instruction → CodeConstraints locals result rest →
      CodeConstraints locals result (.step instruction rest)
  | branch {scrut : Scrutinee} {key : Key} {other : Option Key} {yes no rest : Code} {kind : Option Kind} :
      scrutineeType locals scrut = some kind → keyMatches kind key = true → other.all (keyMatches kind) = true →
      CodeConstraints locals result yes → CodeConstraints locals result no → CodeConstraints locals result rest →
      CodeConstraints locals result (.branch scrut key other yes no rest)

theorem checkCode_sound {locals : List Ty} {result : Ty} {code : Code}
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
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    simp only [checkCode] at h
    cases hs : scrutineeType locals scrut with
    | none => simp [hs] at h
    | some kind =>
      simp only [hs, Bool.and_eq_true_iff] at h
      exact .branch hs h.1.1.1.1 h.1.1.1.2 (ihYes h.1.1.2) (ihNo h.1.2) (ihRest h.2)

end SubtreeProofs.Rust.LookupSource.SourceTypes
