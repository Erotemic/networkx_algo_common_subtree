module

public import SubtreeProofs.Rust.MemoTypeCertificate
public import SubtreeProofs.Rust.MemoHeapExecution
public import SubtreeProofs.Rust.LookupTypeCalls

/-! Recursive operational type preservation from the actual memo source
certificates. Insertion starts with an owned table value; no all-shared input
profile is substituted for its checked argument/return prefix. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Types

open LookupSource LookupSource.Heap LookupSource.SourceTypes

def BodiesTyped (body : Function → Code) : Prop :=
  ∀ function, function ≠ .boxNew → ∃ locals,
    locals.take ((inputs function).length + 1) = output function :: inputs function ∧
    CodeConstraints locals (output function) (body function)

theorem run_typed (body : Function → Code) (hb : BodiesTyped body) (fuel : Nat) :
    CallsTypedWith callOutput (MemoSource.Heap.run body fuel) := by
  induction fuel with
  | zero => intro function cells types memory cell after cost ty _ _ hr; cases hr
  | succ fuel ih =>
    intro function cells types memory cell after cost ty hargs ht hr
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
            simp only [MemoSource.Heap.run, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨alloc_typed hvalue, Extends.append memory [_]⟩
    · simp only [callOutput, hf, ite_false] at ht
      split at ht
      next heq =>
        have heq := sameList_eq heq
        subst types
        cases ht
        obtain ⟨locals, hprefix, hcode⟩ := hb function hf
        simp only [MemoSource.Heap.run, hf, ite_false] at hr
        cases hx : LookupSource.Heap.exec (MemoSource.Heap.run body fuel) (body function) memory (initialLocals cells) with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨result, mem, inner⟩
          simp only [hx, bind, Option.bind] at hr
          cases result with
          | next _ => cases hr
          | returned value =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact exec_typedWith ih (body function) (initial_typed hargs hprefix) hcode hx
      next => cases ht

theorem original_bodies_typed : BodiesTyped Program.body :=
  TypeReader.Certificate.original_boundaries

theorem original_run_typed (fuel : Nat) : CallsTypedWith callOutput (MemoSource.Heap.run Program.body fuel) :=
  run_typed Program.body original_bodies_typed fuel

end SubtreeProofs.Rust.MemoSource.Types
