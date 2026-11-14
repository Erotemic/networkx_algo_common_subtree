module

public import SubtreeProofs.Droschinsky2018.BoundaryStates

/-!
# Connecting-path rewards equal the two boundary-state rewards

A root-to-branch path pair earns an edge reward exactly when its branch root
is the immediate child pair. Otherwise all of its contribution is the
skipped-vertex boundary penalty. No initial-edge label is consulted then.
-/

@[expose] public section

namespace SubtreeProofs.Droschinsky2018

open Droschinsky2016

variable {V W : Type*} [DecidableEq V] [DecidableEq W]

/-- The path-score branch test is exactly the mapped-versus-skipped root test
at the immediate input-child pair. -/
theorem connecting_path_score {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftBase u c : V} {rightBase v d : W}
    (top : V × W) (hc : left.Child leftBase u c) (hd : right.Child rightBase v d)
    (hl : left.Ancestor leftBase c top.1) (hr : right.Ancestor rightBase d top.2) :
    pathScore left right weights penalty s(u,top.1) s(v,top.2) =
      if top = (c,d) then weights.edge s(u,c) s(v,d)
      else skippedScore penalty (left.pathLength c top.1 + right.pathLength d top.2) := by
  classical
  by_cases he : top = (c,d)
  · subst top
    rw [ite_eq_left rfl]
    exact pathScore_direct left right weights penalty _ _ (left.pathLength_adj hc.1) (right.pathLength_adj hd.1)
  · rw [ite_eq_right he]
    have hn : ¬ (pathLength left s(u,top.1) = 1 ∧ pathLength right s(v,top.2) = 1) := by
      rintro ⟨hleft, hright⟩
      change left.pathLength u top.1 = 1 at hleft
      change right.pathLength v top.2 = 1 at hright
      rw [left.pathLength_child_step hc hl] at hleft
      rw [right.pathLength_child_step hd hr] at hright
      have hcl : left.pathLength c top.1 = 0 := by omega
      have hdr : right.pathLength d top.2 = 0 := by omega
      have hce := (left.pathLength_eq_zero c top.1).mp hcl
      have hde := (right.pathLength_eq_zero d top.2).mp hdr
      exact he (Prod.ext hce.symm hde.symm)
    rw [pathScore_skipped left right weights penalty _ _ hn]
    change skippedScore penalty ((left.pathLength u top.1 - 1) + (right.pathLength v top.2 - 1)) = _
    rw [left.pathLength_child_step hc hl, right.pathLength_child_step hd hr]
    simp

/-- Exact edge-plus-continuation score used by the mapped-root matching state. -/
theorem connecting_reward_boundary {left : FiniteTree V} {right : FiniteTree W}
    (weights : Scoring V W) (penalty : WithTop ℝ) {leftBase u c : V} {rightBase v d : W}
    (pairs : Mapping V W) (top : V × W) (hc : left.Child leftBase u c) (hd : right.Child rightBase v d)
    (hl : left.Ancestor leftBase c top.1) (hr : right.Ancestor rightBase d top.2) :
    pathScore left right weights penalty s(u,top.1) s(v,top.2) + score left right weights penalty pairs =
      if top = (c,d) then weights.edge s(u,c) s(v,d) + stateScore left right weights penalty c d pairs top
      else stateScore left right weights penalty c d pairs top := by
  classical
  rw [connecting_path_score weights penalty top hc hd hl hr]
  split
  · rename_i he
    rw [he, stateScore_mapped]
  · unfold stateScore
    exact add_comm _ _

end SubtreeProofs.Droschinsky2018

end
