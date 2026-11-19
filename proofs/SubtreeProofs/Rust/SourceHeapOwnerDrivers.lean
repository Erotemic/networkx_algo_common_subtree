module

public import SubtreeProofs.Rust.LookupOwnerGrowth
public import SubtreeProofs.Rust.LookupSpatialCalls
public import SubtreeProofs.Rust.MemoSpatialCalls

/-! Exact owner ledgers for the unchanged lookup/memo helper drivers at every
successful fuel. The actual checked guarded traces and source local constraints
supply disposable clobbers and bounds. No native height or desired result is an
input. The shared record describes existing execution, not a new interpreter. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Owners

open Spatial

structure ConservingDriver (F : Type) [DecidableEq F] where
  body : F → Code F
  box : F
  argsMatch : F → List Cell → Prop
  callOutput : F → List Ty → Option Ty
  concrete : Nat → CallsFor F
  zero : ∀ function cells memory, concrete 0 function cells memory = none
  box_run : ∀ fuel cells memory output after cost,
    concrete (fuel + 1) box cells memory = some (output, after, cost) →
    ∃ cell, cells = [cell] ∧ output = .owned memory.length ∧ after = memory ++ [cell]
  ordinary : ∀ fuel function cells memory output after cost, function ≠ box → argsMatch function cells →
    concrete (fuel + 1) function cells memory = some (output, after, cost) →
    ∃ (locals : List Ty) (outputType : Ty) (inner : Cost) (good : Frame.CallSafetyFor F), cells.length + 1 ≤ locals.length ∧
      Frame.GuardedWith argsMatch (concrete fuel) good (body function) memory (initialLocals cells) (.returned output) after inner ∧
      SourceTypes.CodeConstraintsWith callOutput locals outputType (body function)

theorem ConservingDriver.grows {F : Type} [DecidableEq F] (driver : ConservingDriver F) (fuel : Nat) :
    CallsGrow driver.argsMatch (driver.concrete fuel) := by
  induction fuel with
  | zero =>
    intro function cells memory cell after cost _ hr
    rw [driver.zero] at hr
    cases hr
  | succ fuel ih =>
    intro function cells memory output after cost hargs hr
    by_cases hf : function = driver.box
    · subst function
      obtain ⟨cell, rfl, rfl, rfl⟩ := driver.box_run fuel cells memory output after cost hr
      refine ⟨Extends.append _ _, ?_⟩
      intro owners ho
      obtain ⟨a, b, rfl, ha, hb⟩ := ho.cons_inv
      cases hb
      refine ⟨a ++ [memory.length], ?_, ?_⟩
      · simpa only [alloc, List.append_nil] using FieldsFootprint.cons
          (Footprint.owned (alloc_fresh memory cell).2.1 (footprint_mono (Extends.append memory [cell]) ha)) FieldsFootprint.nil
      · simp [fresh]
    · obtain ⟨locals, outputType, inner, good, bound, hg, ht⟩ :=
        driver.ordinary fuel function cells memory output after cost hf hargs hr
      have grows := (guarded_grows ih hg ht (initial_bounded bound)).2
      simpa only [resultCells, values_initial cells locals.length bound] using grows

def lookupConservingDriver : ConservingDriver Function where
  body := Program.body
  box := .boxNew
  argsMatch := Frame.ArgsMatch
  callOutput := SourceTypes.callOutput
  concrete := Heap.run Program.body
  zero := by intros; rfl
  box_run := by
    intro fuel cells memory output after cost hr
    simp only [Heap.run, ite_true] at hr
    cases cells with
    | nil => cases hr
    | cons cell rest => cases rest with
      | cons _ _ => cases hr
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        exact ⟨cell, rfl, rfl, rfl⟩
  ordinary := by
    intro fuel function cells memory output after cost hf hargs hr
    have hg := Frame.original_run_safe (fuel + 1) function cells memory hargs hr
    simp only [Frame.RunSafe, hf, ite_false] at hg
    obtain ⟨inner, guarded, _⟩ := hg
    obtain ⟨locals, boundary, typed⟩ := SourceTypes.original_bodies_typed function hf
    exact ⟨locals, SourceTypes.output function, inner, Frame.RunSafe Program.body fuel,
      boundary_bound hf hargs boundary, guarded, typed⟩

theorem lookup_grows (fuel : Nat) : CallsGrow Frame.ArgsMatch (Heap.run Program.body fuel) :=
  lookupConservingDriver.grows fuel

end SubtreeProofs.Rust.LookupSource.Heap.Owners

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap LookupSource.Heap.Owners

def conservingDriver : ConservingDriver Function where
  body := Program.body
  box := .boxNew
  argsMatch := Frame.ArgsMatch
  callOutput := Types.callOutput
  concrete := run Program.body
  zero := by intros; rfl
  box_run := by
    intro fuel cells memory output after cost hr
    simp only [run, ite_true] at hr
    cases cells with
    | nil => cases hr
    | cons cell rest => cases rest with
      | cons _ _ => cases hr
      | nil =>
        simp only [Option.some.injEq, Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, rfl⟩ := hr
        exact ⟨cell, rfl, rfl, rfl⟩
  ordinary := by
    intro fuel function cells memory output after cost hf hargs hr
    have hg := Frame.original_run_safe (fuel + 1) function cells memory hargs hr
    simp only [Frame.RunSafe, hf, ite_false] at hg
    obtain ⟨inner, guarded, _⟩ := hg
    obtain ⟨locals, boundary, typed⟩ := Types.original_bodies_typed function hf
    exact ⟨locals, Types.output function, inner, Frame.RunSafe Program.body fuel,
      MemoSource.Spatial.boundary_bound hf hargs boundary, guarded, typed⟩

theorem run_grows (fuel : Nat) : CallsGrow Frame.ArgsMatch (run Program.body fuel) := conservingDriver.grows fuel

end SubtreeProofs.Rust.MemoSource.Heap
