module

public import SubtreeProofs.Droschinsky2018.Rooted
import Mathlib.Tactic

/-!
# Independent mapped/skipped boundary witnesses

The top pair of a rooted common tree is explicit. Boundary penalties count
vertices skipped before that first mapped pair; internal penalties remain in
the independent abstract-edge score. This distinguishes the paper's diamond
state from a free search for a rooted optimum.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- Feasibility inside the descendant subtrees at a boundary pair. The common
root is `top`, and the input orientations stay fixed throughout recursion. -/
def StateValid (left : FiniteTree V) (right : FiniteTree W) (leftBase : V) (rightBase : W)
    (u : V) (v : W) (pairs : Mapping V W) (top : V × W) : Prop :=
  Valid left right pairs ∧ top ∈ pairs ∧
    (∀ p ∈ pairs, left.Ancestor leftBase top.1 p.1 ∧ right.Ancestor rightBase top.2 p.2) ∧
    left.Ancestor leftBase u top.1 ∧ right.Ancestor rightBase v top.2

/-- Boundary path lengths count one skipped vertex per child descent. -/
noncomputable def stateScore (left : FiniteTree V) (right : FiniteTree W) (weights : Scoring V W)
    (penalty : WithTop ℝ) (u : V) (v : W) (pairs : Mapping V W) (top : V × W) : WithBot ℝ :=
  score left right weights penalty pairs +
    skippedScore penalty (left.pathLength u top.1 + right.pathLength v top.2)

/-- Boundary penalties compose exactly, including the source infinite penalty. -/
theorem skippedScore_add (penalty : WithTop ℝ) (a b : Nat) :
    skippedScore penalty (a+b) = skippedScore penalty a + skippedScore penalty b := by
  by_cases hp : penalty = ⊤
  · subst penalty
    by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp [skippedScore, ha, hb ]
  · simp only [skippedScore, hp, ↓reduceIte]
    rw [← WithBot.coe_add]
    congr 1
    simp [Nat.cast_add, mul_add]

omit [DecidableEq W] in
/-- A mapped boundary has no extra boundary penalty. -/
@[simp] theorem stateScore_mapped (left : FiniteTree V) (right : FiniteTree W)
    (weights : Scoring V W) (penalty : WithTop ℝ) (u : V) (v : W) (pairs : Mapping V W) :
    stateScore left right weights penalty u v pairs (u,v) = score left right weights penalty pairs := by
  simp [stateScore, skippedScore]

/-- Every state has a source-style rooted witness in the fixed orientations. -/
theorem StateValid.toRootedValid {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) :
    RootedValid left right leftBase rightBase pairs := ⟨h.1, top, h.2.1, h.2.2.1⟩

/-- If a boundary root is not mapped, the whole witness fits below a single
child of that root; the child is derived from the actual canonical path. -/
theorem StateValid.skip_left {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) (hn : u ≠ top.1) :
    ∃ c, left.Child leftBase u c ∧ StateValid left right leftBase rightBase c v pairs top := by
  let c := left.firstChild u top.1
  have hc : left.Child leftBase u c := ⟨left.firstChild_adj hn,
    left.ancestor_of_mem_suffix h.2.2.2.1 left.firstChild_ancestor⟩
  exact ⟨c, hc, h.1, h.2.1, h.2.2.1,
    left.suffix_ancestor h.2.2.2.1 left.firstChild_ancestor, h.2.2.2.2⟩

theorem StateValid.skip_right {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) (hn : v ≠ top.2) :
    ∃ d, right.Child rightBase v d ∧ StateValid left right leftBase rightBase u d pairs top := by
  let d := right.firstChild v top.2
  have hd : right.Child rightBase v d := ⟨right.firstChild_adj hn,
    right.ancestor_of_mem_suffix h.2.2.2.2 right.firstChild_ancestor⟩
  exact ⟨d, hd, h.1, h.2.1, h.2.2.1, h.2.2.2.1,
    right.suffix_ancestor h.2.2.2.2 right.firstChild_ancestor⟩

/-- At least one child descent applies in every skipped-root diamond witness. -/
theorem StateValid.skipped_cover {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (h : StateValid left right leftBase rightBase u v pairs top) (hn : top ≠ (u,v)) :
    (∃ c, left.Child leftBase u c ∧ StateValid left right leftBase rightBase c v pairs top) ∨
    (∃ d, right.Child rightBase v d ∧ StateValid left right leftBase rightBase u d pairs top) := by
  by_cases he : u = top.1
  · right
    apply h.skip_right
    intro hv
    exact hn (Prod.ext he.symm hv.symm)
  · exact Or.inl (h.skip_left he)

/-- Every child continuation lifts to a feasible skipped-root parent witness. -/
theorem StateValid.extend_left {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u c : V} {rightBase v : W} {pairs : Mapping V W} {top : V × W}
    (hc : left.Child leftBase u c)
    (h : StateValid left right leftBase rightBase c v pairs top) :
    StateValid left right leftBase rightBase u v pairs top ∧ top ≠ (u,v) := by
  refine ⟨⟨h.1, h.2.1, h.2.2.1, left.ancestor_trans hc.2 h.2.2.2.1, h.2.2.2.2⟩, ?_⟩
  intro he
  have hcu : left.Ancestor leftBase c u := by simpa only [he] using h.2.2.2.1
  exact hc.1.ne (left.ancestor_antisymm hc.2 hcu)

theorem StateValid.extend_right {left : FiniteTree V} {right : FiniteTree W}
    {leftBase u : V} {rightBase v d : W} {pairs : Mapping V W} {top : V × W}
    (hd : right.Child rightBase v d)
    (h : StateValid left right leftBase rightBase u d pairs top) :
    StateValid left right leftBase rightBase u v pairs top ∧ top ≠ (u,v) := by
  refine ⟨⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, right.ancestor_trans hd.2 h.2.2.2.2⟩, ?_⟩
  intro he
  have hdv : right.Ancestor rightBase d v := by simpa only [he] using h.2.2.2.2
  exact hd.1.ne (right.ancestor_antisymm hd.2 hdv)

omit [DecidableEq W] in
/-- The concrete witness score loses exactly one penalty on a left descent. -/
theorem stateScore_step_left {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftBase u c : V} {v : W}
    (pairs : Mapping V W) (top : V × W) (hc : left.Child leftBase u c)
    (htop : left.Ancestor leftBase c top.1) :
    stateScore left right weights penalty u v pairs top = skippedScore penalty 1 +
      stateScore left right weights penalty c v pairs top := by
  unfold stateScore
  have he : left.pathLength u top.1 + right.pathLength v top.2 =
      1 + (left.pathLength c top.1 + right.pathLength v top.2) := by
    rw [left.pathLength_child_step hc htop]
    omega
  rw [he, skippedScore_add]
  ac_rfl

omit [DecidableEq W] in
theorem stateScore_step_right {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {u : V} {rightBase v d : W}
    (pairs : Mapping V W) (top : V × W) (hd : right.Child rightBase v d)
    (htop : right.Ancestor rightBase d top.2) :
    stateScore left right weights penalty u v pairs top = skippedScore penalty 1 +
      stateScore left right weights penalty u d pairs top := by
  unfold stateScore
  have he : left.pathLength u top.1 + right.pathLength v top.2 =
      1 + (left.pathLength u top.1 + right.pathLength d top.2) := by
    rw [right.pathLength_child_step hd htop]
    omega
  rw [he, skippedScore_add]
  ac_rfl

end SubtreeProofs.Droschinsky2018

end
