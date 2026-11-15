module

public import SubtreeProofs.Paper2004.AffinityIsomorphism
import Mathlib.Tactic

/-! # Correct affinity-weighted ordered-isomorphism recurrences

Both root policies optimize the independent operational-pruning witnesses.
This is mathematical ordered-ring correctness, including the author's
positive-affinity extension; it is not a theorem about actual f64 execution.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.AnnotatedIso
namespace AffinityDP

variable {L R K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

def choose (affinity : L → R → K) (first second : Word (L × R)) : Word (L × R) :=
  if score affinity first < score affinity second then second else first

omit [IsStrictOrderedRing K] in
theorem score_choose (affinity : L → R → K) (first second : Word (L × R)) :
    score affinity (choose affinity first second) = max (score affinity first) (score affinity second) := by
  unfold choose
  split
  · rename_i h
    exact (max_eq_right (le_of_lt h)).symm
  · rename_i h
    exact (max_eq_left (le_of_not_gt h)).symm

omit [IsStrictOrderedRing K] in
theorem choose_feasible {P : Word (L × R) → Prop} (affinity : L → R → K)
    {first second : Word (L × R)} (hFirst : P first) (hSecond : P second) :
    P (choose affinity first second) := by
  unfold choose
  split
  · exact hSecond
  · exact hFirst

def level (affinity : L → R → K) (left : Word L) (right : Word R) : Word (L × R) :=
  match left,right with
  | .nil,_ => .nil
  | _,.nil => .nil
  | .node a lh lt,.node b rh rt =>
    let base := choose affinity (level affinity (.node a lh lt) rt) (level affinity lt (.node b rh rt))
    if 0 < affinity a b then
      choose affinity base (.node (a,b) (level affinity lh rh) (level affinity lt rt))
    else base
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

omit [IsStrictOrderedRing K] in
theorem level_sound (affinity : L → R → K) (left : Word L) (right : Word R) :
    LevelWitness affinity (level affinity left right) left right := by
  cases left with
  | nil => simpa only [level] using level_empty affinity .nil right
  | node a lh lt =>
    cases right with
    | nil => simpa only [level] using level_empty affinity (.node a lh lt) .nil
    | node b rh rt =>
      have hRight := level_sound affinity (.node a lh lt) rt
      have hLeft := level_sound affinity lt (.node b rh rt)
      have hBase : LevelWitness affinity
          (choose affinity (level affinity (.node a lh lt) rt) (level affinity lt (.node b rh rt)))
          (.node a lh lt) (.node b rh rt) :=
        choose_feasible (P := fun candidate => LevelWitness affinity candidate (.node a lh lt) (.node b rh rt))
          affinity ⟨hRight.1,hRight.2.1.skip b rh,hRight.2.2⟩
          ⟨hLeft.1.skip a lh,hLeft.2.1,hLeft.2.2⟩
      rw [level]
      split
      · rename_i hp
        exact choose_feasible (P := fun candidate => LevelWitness affinity candidate (.node a lh lt) (.node b rh rt)) affinity hBase
          (level_node a b (level_sound affinity lh rh) (level_sound affinity lt rt) hp)
      · exact hBase
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

/-- Every independently feasible original-identity witness is bounded by the
level recurrence. Zero-affinity root matches are excluded by feasibility. -/
theorem level_upper (affinity : L → R → K) (left : Word L) (right : Word R)
    (candidate : Word (L × R)) (h : LevelWitness affinity candidate left right) :
    score affinity candidate ≤ score affinity (level affinity left right) := by
  cases left with
  | nil =>
    have hn := h.1.eq_nil_of_nil
    cases candidate with
    | nil => simp [level,score]
    | node pair head tail => simp [leftProjection,BinaryTree.map] at hn
  | node a lh lt =>
    cases right with
    | nil =>
      have hn := h.2.1.eq_nil_of_nil
      cases candidate with
      | nil => simp [level,score]
      | node pair head tail => simp [rightProjection,BinaryTree.map] at hn
    | node b rh rt =>
      let base := choose affinity (level affinity (.node a lh lt) rt) (level affinity lt (.node b rh rt))
      have hFull : level affinity (.node a lh lt) (.node b rh rt) =
          if 0 < affinity a b then choose affinity base (.node (a,b) (level affinity lh rh) (level affinity lt rt)) else base := by
        rw [level]
      have hBase : score affinity base ≤ score affinity (level affinity (.node a lh lt) (.node b rh rt)) := by
        rw [hFull]
        split
        · conv_rhs => rw [score_choose]
          exact le_max_left _ _
        · exact le_refl (score affinity base)
      cases candidate with
      | nil => exact (level_sound affinity (.node a lh lt) (.node b rh rt)).2.2.score_nonnegative
      | node pair head tail =>
        have hl : Prunes (.node pair.1 (leftProjection head) (leftProjection tail)) (.node a lh lt) := h.1
        have hr : Prunes (.node pair.2 (rightProjection head) (rightProjection tail)) (.node b rh rt) := h.2.1
        obtain ⟨hp,hh,ht⟩ := (compatible_node affinity pair head tail).mp h.2.2
        rcases hl.first with hDrop | ⟨hA,hHeadLeft,hTailLeft⟩
        · have hu := level_upper affinity lt (.node b rh rt) (.node pair head tail) ⟨hDrop,h.2.1,h.2.2⟩
          have hb : score affinity (level affinity lt (.node b rh rt)) ≤ score affinity base := by
            dsimp only [base]
            rw [score_choose]
            exact le_max_right _ _
          exact hu.trans (hb.trans hBase)
        · rcases hr.first with hDrop | ⟨hB,hHeadRight,hTailRight⟩
          · have hu := level_upper affinity (.node a lh lt) rt (.node pair head tail) ⟨h.1,hDrop,h.2.2⟩
            have hb : score affinity (level affinity (.node a lh lt) rt) ≤ score affinity base := by
              dsimp only [base]
              rw [score_choose]
              exact le_max_left _ _
            exact hu.trans (hb.trans hBase)
          · have hPositive : 0 < affinity a b := by simpa only [hA,hB] using hp
            have hHead := level_upper affinity lh rh head ⟨hHeadLeft,hHeadRight,hh⟩
            have hTail := level_upper affinity lt rt tail ⟨hTailLeft,hTailRight,ht⟩
            have hMatched : score affinity (.node pair head tail) ≤
                score affinity (.node (a,b) (level affinity lh rh) (level affinity lt rt)) := by
              simp only [score,hA,hB]
              linarith
            apply hMatched.trans
            rw [hFull,ite_eq_left hPositive,score_choose]
            exact le_max_right _ _
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

theorem level_correct (affinity : L → R → K) (left : Word L) (right : Word R) :
    IsMaximumLevel affinity (level affinity left right) left right :=
  ⟨level_sound affinity left right,fun candidate h => level_upper affinity left right candidate h⟩

def anywhere (affinity : L → R → K) (left : Word L) (right : Word R) : Word (L × R) :=
  match left,right with
  | .nil,_ => .nil
  | _,.nil => .nil
  | .node a lh lt,.node b rh rt =>
    choose affinity (level affinity (.node a lh lt) (.node b rh rt))
      (choose affinity (choose affinity (anywhere affinity lh (.node b rh rt)) (anywhere affinity lt (.node b rh rt)))
        (choose affinity (anywhere affinity (.node a lh lt) rh) (anywhere affinity (.node a lh lt) rt)))
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

omit [IsStrictOrderedRing K] in
theorem anywhere_sound (affinity : L → R → K) (left : Word L) (right : Word R) :
    AnyWitness affinity (anywhere affinity left right) left right := by
  cases left with
  | nil => simpa only [anywhere] using (level_empty affinity .nil right).any
  | node a lh lt =>
    cases right with
    | nil => simpa only [anywhere] using (level_empty affinity (.node a lh lt) .nil).any
    | node b rh rt =>
      have hLH := anywhere_sound affinity lh (.node b rh rt)
      have hLT := anywhere_sound affinity lt (.node b rh rt)
      have hRH := anywhere_sound affinity (.node a lh lt) rh
      have hRT := anywhere_sound affinity (.node a lh lt) rt
      rw [anywhere]
      apply choose_feasible (P := fun candidate => AnyWitness affinity candidate (.node a lh lt) (.node b rh rt))
        affinity (level_sound affinity _ _).any
      apply choose_feasible (P := fun candidate => AnyWitness affinity candidate (.node a lh lt) (.node b rh rt)) affinity
      · exact choose_feasible (P := fun candidate => AnyWitness affinity candidate (.node a lh lt) (.node b rh rt))
          affinity ⟨hLH.1.head a lt,hLH.2⟩ ⟨hLT.1.tail a lh,hLT.2⟩
      · exact choose_feasible (P := fun candidate => AnyWitness affinity candidate (.node a lh lt) (.node b rh rt))
          affinity ⟨hRH.1,hRH.2.1.head b rt,hRH.2.2⟩ ⟨hRT.1,hRT.2.1.tail b rh,hRT.2.2⟩
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

theorem anywhere_upper (affinity : L → R → K) (left : Word L) (right : Word R)
    (candidate : Word (L × R)) (h : AnyWitness affinity candidate left right) :
    score affinity candidate ≤ score affinity (anywhere affinity left right) := by
  cases left with
  | nil =>
    have hn := h.1.eq_nil_of_nil
    cases candidate with
    | nil => simp [anywhere,score]
    | node pair head tail => simp [leftProjection,BinaryTree.map] at hn
  | node a lh lt =>
    cases right with
    | nil =>
      have hn := h.2.1.eq_nil_of_nil
      cases candidate with
      | nil => simp [anywhere,score]
      | node pair head tail => simp [rightProjection,BinaryTree.map] at hn
    | node b rh rt =>
      have hFull : score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) =
          max (score affinity (level affinity (.node a lh lt) (.node b rh rt)))
            (max (max (score affinity (anywhere affinity lh (.node b rh rt))) (score affinity (anywhere affinity lt (.node b rh rt))))
              (max (score affinity (anywhere affinity (.node a lh lt) rh)) (score affinity (anywhere affinity (.node a lh lt) rt)))) := by
        rw [anywhere]
        simp only [score_choose]
      have hLevel : score affinity (level affinity (.node a lh lt) (.node b rh rt)) ≤
          score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) := by rw [hFull]; exact le_max_left _ _
      have hLH : score affinity (anywhere affinity lh (.node b rh rt)) ≤
          score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) := by
        rw [hFull]
        exact (le_max_left _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hLT : score affinity (anywhere affinity lt (.node b rh rt)) ≤
          score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) := by
        rw [hFull]
        exact (le_max_right _ _).trans ((le_max_left _ _).trans (le_max_right _ _))
      have hRH : score affinity (anywhere affinity (.node a lh lt) rh) ≤
          score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) := by
        rw [hFull]
        exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      have hRT : score affinity (anywhere affinity (.node a lh lt) rt) ≤
          score affinity (anywhere affinity (.node a lh lt) (.node b rh rt)) := by
        rw [hFull]
        exact (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
      rcases h.1.first with hLeft | hLeft | hLeft
      · rcases h.2.1.first with hRight | hRight | hRight
        · exact (level_upper affinity _ _ candidate ⟨hLeft,hRight,h.2.2⟩).trans hLevel
        · exact (anywhere_upper affinity _ _ candidate ⟨h.1,hRight,h.2.2⟩).trans hRH
        · exact (anywhere_upper affinity _ _ candidate ⟨h.1,hRight,h.2.2⟩).trans hRT
      · exact (anywhere_upper affinity _ _ candidate ⟨hLeft,h.2⟩).trans hLH
      · exact (anywhere_upper affinity _ _ candidate ⟨hLeft,h.2⟩).trans hLT
termination_by left.numNodes+right.numNodes
decreasing_by all_goals simp_all only [BinaryTree.numNodes]; omega

theorem anywhere_correct (affinity : L → R → K) (left : Word L) (right : Word R) :
    IsMaximumAny affinity (anywhere affinity left right) left right :=
  ⟨anywhere_sound affinity left right,fun candidate h => anywhere_upper affinity left right candidate h⟩

end AffinityDP
end SubtreeProofs.Paper2004.AnnotatedIso

end
