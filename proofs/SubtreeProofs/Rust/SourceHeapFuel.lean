module

public import SubtreeProofs.Rust.MemoHeapExecution

/-! Nesting fuel extension for the actual existing helper heaps. Every completed
run retains its exact cells, memory and complete source cost at larger fuel.
No native shape, source result, ownership or safety premise is needed. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

def CallsExtend {F : Type} (first second : CallsFor F) : Prop :=
  ∀ function cells memory cell after cost, first function cells memory = some (cell, after, cost) →
    second function cells memory = some (cell, after, cost)

theorem action_extends {F : Type} {first second : CallsFor F} (hc : CallsExtend first second)
    {memory after : Memory} {env next : Locals} {instruction : Action F} {cost : Cost}
    (h : action first memory env instruction = some (next, after, cost)) :
    action second memory env instruction = some (next, after, cost) := by
  cases instruction with
  | scope _ | assign _ _ | dropMoved _ => exact h
  | call function args slot =>
    simp only [action, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨values, middle⟩, ha, ⟨cell, memory, inner⟩, run, last⟩ := h
    exact ⟨_, ha, _, hc _ _ _ _ _ _ run, last⟩

theorem selectBranch_extends {α : Type} (actual key : Key) (other : Option Key)
    {yes no yes' no' : Option α}
    (hy : ∀ value, yes = some value → yes' = some value)
    (hn : ∀ value, no = some value → no' = some value)
    {value : α} (h : selectBranch actual key other (fun _ => yes) (fun _ => no) = some value) :
    selectBranch actual key other (fun _ => yes') (fun _ => no') = some value := by
  unfold selectBranch at h ⊢
  split at h
  next same => simpa only [same, ite_true] using hy _ h
  next different =>
    simp only [different, ite_false]
    split at h
    next fallback => simpa only [fallback, ite_true] using hn _ h
    next => cases h

theorem exec_extends {F : Type} {first second : CallsFor F} (hc : CallsExtend first second)
    (code : Code F) {memory after : Memory} {env : Locals} {result : Result} {cost : Cost}
    (h : exec first code memory env = some (result, after, cost)) :
    exec second code memory env = some (result, after, cost) := by
  induction code generalizing memory after env result cost with
  | done => exact h
  | ret => exact h
  | step instruction rest ih =>
    simp only [exec, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨middle, memory, firstCost⟩, ha, ⟨result, after, lastCost⟩, hr, last⟩ := h
    exact ⟨_, action_extends hc ha, _, ih hr, last⟩
  | branch scrut key other yes no rest ihYes ihNo ihRest =>
    simp only [exec, bind, Option.bind_eq_some_iff] at h ⊢
    obtain ⟨⟨actual, middle⟩, hs, ⟨result, memory, firstCost⟩, branch, last⟩ := h
    have selected := selectBranch_extends actual key other (fun _ hp => ihYes hp) (fun _ hp => ihNo hp) branch
    refine ⟨_, hs, _, selected, ?_⟩
    cases result with
    | returned cell => exact last
    | next locals =>
      simp only [Option.bind_eq_some_iff] at last ⊢
      obtain ⟨⟨result, memory, lastCost⟩, hr, last⟩ := last
      exact ⟨_, ihRest hr, last⟩

theorem run_fuel_enlarge (body : Function → Code) {small large : Nat} (bound : small ≤ large) :
    CallsExtend (run body small) (run body large) := by
  induction small generalizing large with
  | zero => intro function cells memory cell after cost h; cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      intro function cells memory cell after cost h
      by_cases box : function = .boxNew
      · simpa only [run, box, ite_true] using h
      · simp only [run, box, ite_false, bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨⟨result, memory, inner⟩, hr, last⟩ := h
        exact ⟨_, exec_extends (ih (by omega)) _ hr, last⟩

end SubtreeProofs.Rust.LookupSource.Heap

namespace SubtreeProofs.Rust.MemoSource.Heap

open LookupSource LookupSource.Heap

theorem run_fuel_enlarge (body : Function → MemoSource.Code) {small large : Nat} (bound : small ≤ large) :
    LookupSource.Heap.CallsExtend (run body small) (run body large) := by
  induction small generalizing large with
  | zero => intro function cells memory cell after cost h; cases h
  | succ small ih =>
    cases large with
    | zero => omega
    | succ large =>
      intro function cells memory cell after cost h
      by_cases box : function = .boxNew
      · simpa only [run, box, ite_true] using h
      · simp only [run, box, ite_false, bind, Option.bind_eq_some_iff] at h ⊢
        obtain ⟨⟨result, memory, inner⟩, hr, last⟩ := h
        exact ⟨_, LookupSource.Heap.exec_extends (ih (by omega)) _ hr, last⟩

end SubtreeProofs.Rust.MemoSource.Heap
