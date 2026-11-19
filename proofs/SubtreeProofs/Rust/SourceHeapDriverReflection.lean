module

public import SubtreeProofs.Rust.LookupHeapReflection
public import SubtreeProofs.Rust.MemoHeapExecution

/-! The existing lookup and memo helper drivers reflect successful concrete
runs at exactly the same call fuel, value and cost. A shared induction consumes
the actual successor equations and concrete zero case; no interpreter is added. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

structure ReflectingDriver (F : Type) [DecidableEq F] where
  body : F → Code F
  box : F
  entry : F → LookupEvents.Events
  concrete : Nat → CallsFor F
  source : Nat → CalleesFor F
  concrete_zero : ∀ function cells memory, concrete 0 function cells memory = none
  concrete_succ : ∀ fuel function cells memory, concrete (fuel + 1) function cells memory =
    (if function = box then
      match cells with
      | [cell] => some ((alloc memory cell).1, (alloc memory cell).2, ⟨1, entry function⟩)
      | _ => none
    else do
      let (result, after, work) ← exec (concrete fuel) (body function) memory (initialLocals cells)
      match result with
      | .next _ => none
      | .returned cell => some (cell, after, (⟨1, entry function⟩ : Cost).plus work))
  source_succ : ∀ fuel function values, source (fuel + 1) function values =
    (if function = box then
      match values with
      | [value] => some (.boxed value, ⟨1, entry function⟩)
      | _ => none
    else do
      let (outcome, work) ← LookupSource.exec (source fuel) (body function) (initialEnv values)
      match outcome with
      | .next _ => none
      | .returned value => some (value, (⟨1, entry function⟩ : Cost).plus work))

theorem ReflectingDriver.reflect {F : Type} [DecidableEq F] (driver : ReflectingDriver F) (fuel : Nat) :
    CallsReflect (driver.concrete fuel) (driver.source fuel) := by
  induction fuel with
  | zero =>
    intro function memory cells values cell after cost _ hr
    rw [driver.concrete_zero] at hr
    cases hr
  | succ fuel ih =>
    intro function memory cells values cell after cost hargs hr
    rw [driver.concrete_succ] at hr
    by_cases hf : function = driver.box
    · subst function
      simp only [ite_true] at hr
      cases hargs with
      | nil => cases hr
      | cons first rest =>
        cases rest with
        | cons _ _ => cases hr
        | nil =>
          simp only [Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          exact ⟨_, by rw [driver.source_succ]; simp, alloc_rep first, Extends.append memory [_]⟩
    · simp only [hf, ite_false] at hr
      cases hx : exec (driver.concrete fuel) (driver.body function) memory (initialLocals cells) with
      | none => simp [hx] at hr
      | some packet =>
        rcases packet with ⟨result, final, work⟩
        cases result with
        | next state => simp [hx] at hr
        | returned output =>
          simp only [hx, Bind.bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at hr
          obtain ⟨rfl, rfl, rfl⟩ := hr
          obtain ⟨outcome, hs, ho, hext⟩ := exec_reflect ih (driver.body function) (initial_rep hargs) hx
          cases outcome with
          | next _ => cases ho
          | returned value =>
            exact ⟨value, by rw [driver.source_succ]; simp only [hf, ite_false, hs, Bind.bind, Option.bind], ho, hext⟩

def lookupReflectingDriver (body : Function → Code) : ReflectingDriver Function where
  body := body
  box := .boxNew
  entry := entryEvents
  concrete := run body
  source := LookupSource.run body
  concrete_zero := by intros; rfl
  concrete_succ := by intros; rfl
  source_succ := by intros; rfl

theorem run_reflect (body : Function → Code) (fuel : Nat) : CallsReflect (run body fuel) (LookupSource.run body fuel) :=
  (lookupReflectingDriver body).reflect fuel

end SubtreeProofs.Rust.LookupSource.Heap

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap

def memoReflectingDriver (body : Function → MemoSource.Code) : ReflectingDriver Function where
  body := body
  box := .boxNew
  entry := MemoSource.entryEvents
  concrete := run body
  source := MemoSource.run body
  concrete_zero := by intros; rfl
  concrete_succ := by intros; rfl
  source_succ := by intros; rfl

theorem run_reflect (body : Function → MemoSource.Code) (fuel : Nat) :
    CallsReflect (run body fuel) (MemoSource.run body fuel) :=
  (memoReflectingDriver body).reflect fuel

end SubtreeProofs.Rust.MemoSource.Heap
