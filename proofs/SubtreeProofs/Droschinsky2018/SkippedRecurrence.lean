module

public import SubtreeProofs.Droschinsky2018.BoundaryStates
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

/-!
# The skipped-root recurrence against independent witness maxima

Values below optimize finite boundary witnesses. The recurrence is a theorem
about that independently defined family, including empty child families and
infinite penalties; it is not used as their definition.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [Fintype V] [Fintype W] [DecidableEq V] [DecidableEq W]

abbrev BoundaryWitness (V W : Type*) := Mapping V W × (V × W)

noncomputable def stateFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) : Finset (BoundaryWitness V W) := by
  classical
  exact ((Finset.univ.powerset).product Finset.univ).filter
    (fun witness => StateValid left right leftBase rightBase u v witness.1 witness.2)

@[simp] theorem mem_stateFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) (w : BoundaryWitness V W) :
    w ∈ stateFeasible left right leftBase rightBase u v ↔ StateValid left right leftBase rightBase u v w.1 w.2 := by
  classical
  simp [stateFeasible]

noncomputable def skippedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) : Finset (BoundaryWitness V W) := by
  classical
  exact (stateFeasible left right leftBase rightBase u v).filter (fun w => w.2 ≠ (u,v))

@[simp] theorem mem_skippedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) (w : BoundaryWitness V W) :
    w ∈ skippedFeasible left right leftBase rightBase u v ↔
      StateValid left right leftBase rightBase u v w.1 w.2 ∧ w.2 ≠ (u,v) := by
  classical
  simp [skippedFeasible]

noncomputable def allStateValue (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) : WithBot ℝ :=
  (stateFeasible left right leftBase rightBase u v).sup (fun w => stateScore left right weights penalty u v w.1 w.2)

noncomputable def skippedValue (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) : WithBot ℝ :=
  (skippedFeasible left right leftBase rightBase u v).sup (fun w => stateScore left right weights penalty u v w.1 w.2)

noncomputable def mappedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) : Finset (BoundaryWitness V W) := by
  classical
  exact (stateFeasible left right leftBase rightBase u v).filter (fun w => w.2 = (u,v))

@[simp] theorem mem_mappedFeasible (left : FiniteTree V) (right : FiniteTree W)
    (leftBase : V) (rightBase : W) (u : V) (v : W) (w : BoundaryWitness V W) :
    w ∈ mappedFeasible left right leftBase rightBase u v ↔
      StateValid left right leftBase rightBase u v w.1 w.2 ∧ w.2 = (u,v) := by
  classical
  simp [mappedFeasible]

noncomputable def mappedValue (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) : WithBot ℝ :=
  (mappedFeasible left right leftBase rightBase u v).sup (fun w => stateScore left right weights penalty u v w.1 w.2)

noncomputable def childVertices (tree : FiniteTree V) (base u : V) : Finset V := by
  classical
  exact Finset.univ.filter (tree.Child base u)

omit [DecidableEq V] in
@[simp] theorem mem_childVertices (tree : FiniteTree V) (base u c : V) :
    c ∈ childVertices tree base u ↔ tree.Child base u c := by
  classical
  simp [childVertices]

theorem stateScore_le_allStateValue {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftBase u : V} {rightBase v : W}
    {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) :
    stateScore left right weights penalty u v pairs top ≤ allStateValue left right weights penalty leftBase rightBase u v :=
  Finset.le_sup (s := stateFeasible left right leftBase rightBase u v)
    (f := fun w => stateScore left right weights penalty u v w.1 w.2)
    ((mem_stateFeasible left right leftBase rightBase u v (pairs,top)).mpr h)

theorem stateScore_le_skippedValue {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftBase u : V} {rightBase v : W}
    {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) (hn : top ≠ (u,v)) :
    stateScore left right weights penalty u v pairs top ≤ skippedValue left right weights penalty leftBase rightBase u v :=
  Finset.le_sup (s := skippedFeasible left right leftBase rightBase u v)
    (f := fun w => stateScore left right weights penalty u v w.1 w.2)
    ((mem_skippedFeasible left right leftBase rightBase u v (pairs,top)).mpr ⟨h, hn⟩)

/-- The two states exactly partition the independent boundary objective. -/
theorem allStateValue_eq_max (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    allStateValue left right weights penalty leftBase rightBase u v =
      max (mappedValue left right weights penalty leftBase rightBase u v)
        (skippedValue left right weights penalty leftBase rightBase u v) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro w hw
    have hv := (mem_stateFeasible left right leftBase rightBase u v w).mp hw
    by_cases he : w.2 = (u,v)
    · have hle := Finset.le_sup (s := mappedFeasible left right leftBase rightBase u v)
        (f := fun w => stateScore left right weights penalty u v w.1 w.2)
        ((mem_mappedFeasible left right leftBase rightBase u v w).mpr ⟨hv, he⟩)
      exact hle.trans (le_max_left _ _)
    · exact (stateScore_le_skippedValue weights penalty hv he).trans (le_max_right _ _)
  · apply max_le
    · apply Finset.sup_le
      intro w hw
      exact stateScore_le_allStateValue weights penalty
        ((mem_mappedFeasible left right leftBase rightBase u v w).mp hw).1
    · apply Finset.sup_le
      intro w hw
      exact stateScore_le_allStateValue weights penalty
        ((mem_skippedFeasible left right leftBase rightBase u v w).mp hw).1

/-- Addition distributes over finite maxima in the extended-real score domain,
including the empty family whose maximum is negative infinity. -/
theorem add_finset_sup {A : Type*} (s : Finset A) (f : A → WithBot ℝ) (a : WithBot ℝ) :
    a + s.sup f = s.sup (fun x => a + f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => simp [Finset.sup_insert, ih, add_max]

/-- 2018 Lemma 5's diamond recurrence. Each feasible skipped-root witness
admits a child descent; every child witness lifts back with exactly one penalty. -/
theorem skipped_recurrence (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    skippedValue left right weights penalty leftBase rightBase u v = skippedScore penalty 1 +
      max ((childVertices left leftBase u).sup (fun c => allStateValue left right weights penalty leftBase rightBase c v))
        ((childVertices right rightBase v).sup (fun d => allStateValue left right weights penalty leftBase rightBase u d)) := by
  classical
  apply le_antisymm
  · apply Finset.sup_le
    intro w hw
    obtain ⟨hv, hn⟩ := (mem_skippedFeasible _ _ _ _ _ _ _).mp hw
    rcases hv.skipped_cover hn with ⟨c, hc, hs⟩ | ⟨d, hd, hs⟩
    · rw [stateScore_step_left weights penalty w.1 w.2 hc hs.2.2.2.1]
      apply add_le_add le_rfl
      have hscore := stateScore_le_allStateValue weights penalty hs
      have hchild := Finset.le_sup (s := childVertices left leftBase u)
        (f := fun c => allStateValue left right weights penalty leftBase rightBase c v)
        ((mem_childVertices left leftBase u c).mpr hc)
      exact hscore.trans (hchild.trans (le_max_left _ _))
    · rw [stateScore_step_right weights penalty w.1 w.2 hd hs.2.2.2.2]
      apply add_le_add le_rfl
      have hscore := stateScore_le_allStateValue weights penalty hs
      have hchild := Finset.le_sup (s := childVertices right rightBase v)
        (f := fun d => allStateValue left right weights penalty leftBase rightBase u d)
        ((mem_childVertices right rightBase v d).mpr hd)
      exact hscore.trans (hchild.trans (le_max_right _ _))
  · rw [add_max, add_finset_sup, add_finset_sup]
    apply max_le
    · apply Finset.sup_le
      intro c hc
      have hchild := (mem_childVertices _ _ _ _).mp hc
      rw [allStateValue, add_finset_sup]
      apply Finset.sup_le
      intro w hw
      have hv := (mem_stateFeasible _ _ _ _ _ _ _).mp hw
      have hp := hv.extend_left hchild
      rw [← stateScore_step_left weights penalty w.1 w.2 hchild hv.2.2.2.1]
      exact stateScore_le_skippedValue weights penalty hp.1 hp.2
    · apply Finset.sup_le
      intro d hd
      have hchild := (mem_childVertices _ _ _ _).mp hd
      rw [allStateValue, add_finset_sup]
      apply Finset.sup_le
      intro w hw
      have hv := (mem_stateFeasible _ _ _ _ _ _ _).mp hw
      have hp := hv.extend_right hchild
      rw [← stateScore_step_right weights penalty w.1 w.2 hchild hv.2.2.2.2]
      exact stateScore_le_skippedValue weights penalty hp.1 hp.2

/-- The source's explicit mapped/skipped form of the diamond recurrence. -/
theorem skipped_recurrence_two_state (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (leftBase : V) (rightBase : W) (u : V) (v : W) :
    skippedValue left right weights penalty leftBase rightBase u v = skippedScore penalty 1 +
      max ((childVertices left leftBase u).sup (fun c =>
          max (mappedValue left right weights penalty leftBase rightBase c v)
            (skippedValue left right weights penalty leftBase rightBase c v)))
        ((childVertices right rightBase v).sup (fun d =>
          max (mappedValue left right weights penalty leftBase rightBase u d)
            (skippedValue left right weights penalty leftBase rightBase u d))) := by
  simpa only [allStateValue_eq_max] using skipped_recurrence left right weights penalty leftBase rightBase u v

end SubtreeProofs.Droschinsky2018

end
