module

public import SubtreeProofs.Rust.SourceEvalTypeExecution
public import SubtreeProofs.Rust.SourceEvalTypeCertificate

/-! Typed initial partial locals and recursive call discharge for every
completed actual-program run. Intrinsics are proved from their scalar/Box
semantics. No input consistency, native refinement or global work bound is
assumed. Addressed owners/storage/loans remain separate obligations. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Types

open LookupSource Heap Partial

theorem snapshotFields_slot {values : List Value} {types : List Ty}
    (h : SnapshotFieldsTyped values types) (index : Nat) {value : Value}
    (hg : values[index]? = some value) : ∃ ty, types[index]? = some ty ∧ SnapshotTyped value ty := by
  induction index generalizing values types with
  | zero => cases h with
    | nil => cases hg
    | cons first rest => cases hg; exact ⟨_, rfl, first⟩
  | succ index ih => cases h with
    | nil => cases hg
    | cons first rest => exact ih rest hg

theorem initial_typed {args : List Value} {types locals : List Ty} {output : Ty}
    (hargs : SnapshotFieldsTyped args types) (hb : locals.take (types.length + 1) = output :: types) :
    LocalsTyped locals (initialState args) := by
  intro slot ty hlocal
  by_cases hz : slot = 0
  · subst slot
    simpa only [initialState, Locals.lift, initialEnv, ite_true] using SlotTyped.empty ty
  · cases hg : args[slot - 1]? with
    | none =>
      simpa only [initialState, Locals.lift, initialEnv, hz, ite_false, hg] using SlotTyped.empty ty
    | some value =>
      obtain ⟨actual, ht, hv⟩ := snapshotFields_slot hargs (slot - 1) hg
      have hi : slot - 1 < types.length := List.getElem?_eq_some_iff.mp ht |>.choose
      have hs : slot = (slot - 1) + 1 := by omega
      have hl : locals[slot]? = (output :: types)[slot]? := by
        rw [← hb]
        exact (List.getElem?_take_of_lt (by omega)).symm
      rw [hs, List.getElem?_cons_succ, ht] at hl
      rw [← hs, hlocal] at hl
      cases hl
      simpa only [initialState, Locals.lift, initialEnv, hz, ite_false, hg] using ofValue_typed hv

theorem typed_u32 {value : Value} (h : SnapshotTyped value .u32) :
    ∃ number, value = .number number ∧ number < 2^32 := by
  cases h with
  | number bound => exact ⟨_, rfl, bound⟩
  | node shape _ => cases shape

theorem numberOption_typed (value : Option Nat) (h : ∀ n, value = some n → n < 2^32) :
    SnapshotTyped (encodeNumberOption value) (.option .u32) := by
  cases value with
  | none => exact .node (.optionNone _) .nil
  | some n => exact .node (.optionSome _) (.cons (.number (h n rfl)) .nil)

theorem checkedAdd32_typed (left right : Nat) :
    SnapshotTyped (encodeNumberOption (checkedAdd32 left right)) (.option .u32) :=
  numberOption_typed _ (fun _ h => (checkedAdd32_success h).2)

theorem callOutput_standard {function : SourceEval.Function} {types : List Ty} {ty : Ty}
    (hf : function ≠ .boxNew) (h : callOutput function types = some ty) :
    types = inputs function ∧ ty = output function := by
  simp only [callOutput, hf, ite_false] at h
  split at h
  next he => cases h; exact ⟨SourceTypes.sameList_eq he, rfl⟩
  next => cases h

def BodiesTyped (body : SourceEval.Function → SourceEval.Code) : Prop :=
  ∀ function, function ≠ .boxNew → function ≠ .checkedAdd → ∃ locals,
    locals.take ((inputs function).length + 1) = output function :: inputs function ∧
    CodeConstraints locals (output function) (body function)

theorem run_ordinary (body : SourceEval.Function → SourceEval.Code) (fuel : Nat)
    (function : SourceEval.Function) (args : List Value) (hf : function ≠ .boxNew) (ha : function ≠ .checkedAdd) :
    run body (fuel + 1) function args = (do
      let (result, work) ← SourceEval.exec (run body fuel) (body function) (initialState args)
      match result with
      | .next _ => none
      | .returned value => some (value, (SourceEval.Cost.entry function).plus work)) := by
  cases function <;> first | contradiction | rfl

theorem run_typed (body : SourceEval.Function → SourceEval.Code) (hb : BodiesTyped body) (fuel : Nat) :
    CallsTyped (run body fuel) := by
  induction fuel with
  | zero => intro function args types value cost ty _ _ hr; cases hr
  | succ fuel ih =>
    intro function args types value cost ty hargs ht hr
    by_cases hf : function = .boxNew
    · subst function
      simp only [callOutput, ite_true] at ht
      cases types with
      | nil => cases ht
      | cons inner rest => cases rest with
        | cons _ _ => cases ht
        | nil =>
          cases ht
          cases hargs with
          | cons hvalue htail =>
            cases htail
            simp only [run, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact .owned hvalue
    · obtain ⟨rfl, rfl⟩ := callOutput_standard hf ht
      by_cases ha : function = .checkedAdd
      · subst function
        cases hargs with
        | cons hl rest => cases rest with
          | cons hrTy rest =>
            cases rest
            obtain ⟨left, rfl, leftBound⟩ := typed_u32 hl
            obtain ⟨right, rfl, rightBound⟩ := typed_u32 hrTy
            change (if left < 2^32 ∧ right < 2^32 then
              some (encodeNumberOption (checkedAdd32 left right), SourceEval.Cost.entry .checkedAdd)
              else none) = some (value, cost) at hr
            simp only [leftBound, rightBound, and_self, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact checkedAdd32_typed left right
      · obtain ⟨locals, hprefix, hcode⟩ := hb function hf ha
        rw [run_ordinary body fuel function args hf ha] at hr
        cases hx : SourceEval.exec (run body fuel) (body function) (initialState args) with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨result, inner⟩
          simp only [hx, bind, Option.bind] at hr
          cases result with
          | next _ => cases hr
          | returned result =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl⟩ := hr
            exact exec_typed ih (initial_typed hargs hprefix) hcode hx

theorem ordinary_mem_helpers (function : SourceEval.Function) (hf : function ≠ .boxNew)
    (ha : function ≠ .checkedAdd) : function ∈ ProgramReader.helpers := by
  cases function <;> first | contradiction | decide +kernel

theorem original_bodies_typed : BodiesTyped SourceEval.Certificate.original.body :=
  fun function hf ha => TypeReader.Certificate.original_boundaries function (ordinary_mem_helpers function hf ha)

theorem original_run_typed (fuel : Nat) : CallsTyped (run SourceEval.Certificate.original.body fuel) :=
  run_typed _ original_bodies_typed fuel

end SubtreeProofs.Rust.SourceEval.Types
