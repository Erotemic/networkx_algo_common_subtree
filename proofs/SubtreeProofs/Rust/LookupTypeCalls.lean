module

public import SubtreeProofs.Rust.LookupTypeExecution
public import SubtreeProofs.Rust.LookupTypeCertificate

/-! Recursive discharge of type-preserving call contracts for the actual
addressed programs. Success is conditional on the unchanged execution, not
inferred from a static check. Spatial uniqueness and lifetimes remain separate. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.SourceTypes

open Heap

theorem fieldsTyped_slot {memory : Memory} {cells : List Cell} {types : List Ty}
    (h : FieldsTyped memory cells types) (index : Nat) {cell : Cell}
    (hc : cells[index]? = some cell) : ∃ ty, types[index]? = some ty ∧ Typed memory cell ty := by
  induction index generalizing cells types with
  | zero => cases h with
    | nil => cases hc
    | cons first rest => cases hc; exact ⟨_, rfl, first⟩
  | succ index ih => cases h with
    | nil => cases hc
    | cons first rest => exact ih rest hc

theorem initial_typed {memory : Memory} {cells : List Cell} {types locals : List Ty} {result : Ty}
    (hargs : FieldsTyped memory cells types) (hb : locals.take (types.length + 1) = result :: types) :
    EnvTyped memory locals (initialLocals cells) := by
  intro slot cell hc
  by_cases hzero : slot = 0
  · simp [initialLocals, hzero] at hc
  · simp only [initialLocals, hzero, ite_false] at hc
    obtain ⟨ty, ht, hv⟩ := fieldsTyped_slot hargs (slot - 1) hc
    have hi : slot - 1 < types.length := List.getElem?_eq_some_iff.mp ht |>.choose
    have hs : slot = (slot - 1) + 1 := by omega
    have hl : locals[slot]? = (result :: types)[slot]? := by
      rw [← hb]
      exact (List.getElem?_take_of_lt (by omega)).symm
    rw [hs, List.getElem?_cons_succ, ht] at hl
    exact ⟨ty, by simpa only [← hs] using hl, hv⟩

theorem alloc_typed {memory : Memory} {cell : Cell} {ty : Ty} (h : Typed memory cell ty) :
    Typed (alloc memory cell).2 (alloc memory cell).1 (.owned ty) := by
  apply Typed.owned (alloc_fresh memory cell).2.1
  exact typed_mono (Extends.append memory [cell]) h

def BodiesTyped (body : Function → Code) : Prop :=
  ∀ function, function ≠ .boxNew → ∃ locals,
    locals.take ((inputs function).length + 1) = output function :: inputs function ∧
    CodeConstraints locals (output function) (body function)

theorem run_typed (body : Function → Code) (hb : BodiesTyped body) (fuel : Nat) :
    CallsTyped (Heap.run body fuel) := by
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
            simp only [Heap.run, ite_true, Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact ⟨alloc_typed hvalue, Extends.append memory [_]⟩
    · simp only [callOutput, hf, ite_false] at ht
      split at ht
      next heq =>
        have heq := sameList_eq heq
        subst types
        cases ht
        obtain ⟨locals, hprefix, hcode⟩ := hb function hf
        simp only [Heap.run, hf, ite_false] at hr
        cases hx : Heap.exec (Heap.run body fuel) (body function) memory (initialLocals cells) with
        | none => simp [hx] at hr
        | some pair =>
          rcases pair with ⟨result, mem, inner⟩
          simp only [hx, bind, Option.bind] at hr
          cases result with
          | next _ => cases hr
          | returned value =>
            simp only [Option.some.injEq, Prod.mk.injEq] at hr
            obtain ⟨rfl, rfl, rfl⟩ := hr
            exact exec_typed ih (body function) (initial_typed hargs hprefix) hcode hx
      next => cases ht

theorem original_bodies_typed : BodiesTyped Program.body :=
  TypeReader.check_boundaries TypeReader.Certificate.original_checked

theorem mutant_bodies_typed : BodiesTyped ExtraCompare.body :=
  TypeReader.check_boundaries TypeReader.Certificate.mutant_checked

theorem original_run_typed (fuel : Nat) : CallsTyped (Heap.run Program.body fuel) :=
  run_typed Program.body original_bodies_typed fuel

theorem mutant_run_typed (fuel : Nat) : CallsTyped (Heap.run ExtraCompare.body fuel) :=
  run_typed ExtraCompare.body mutant_bodies_typed fuel

end SubtreeProofs.Rust.LookupSource.SourceTypes
