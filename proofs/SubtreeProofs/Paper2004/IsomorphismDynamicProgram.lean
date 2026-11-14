module

public import SubtreeProofs.Paper2004.OrderedIsomorphism
import Mathlib.Tactic

/-!
# Constructive ordered-isomorphism optima

The level state selects an ordered sequence of retained children under the two
fixed roots. The arbitrary-root state also searches below either current root.
Whole-subtree skips preserve adjacency, unlike contraction/embedding skips.
Soundness and completeness refer to the independent tree selection relations.
-/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree
namespace OrderedIsoDP

/-- Select a larger child forest, retaining the first witness on ties. -/
def longer (first second : List OrderedTree) : List OrderedTree :=
  if forestEdgeCount first < forestEdgeCount second then second else first

@[simp] theorem longer_edges (first second : List OrderedTree) :
    forestEdgeCount (longer first second) = max (forestEdgeCount first) (forestEdgeCount second) := by
  unfold longer
  split <;> omega

/-- Root-preserving common ordered forest, including its actual tree witness. -/
def level (left right : List OrderedTree) : List OrderedTree :=
  match left,right with
  | [],_ => []
  | _,[] => []
  | .node lh::lt,.node rh::rt =>
    longer (longer (.node (level lh rh)::level lt rt) (level lt (.node rh::rt)))
      (level (.node lh::lt) rt)
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- The same common subtree may choose either input root at any descendant. -/
def anywhere (left right : List OrderedTree) : List OrderedTree :=
  match left,right with
  | [],_ => []
  | _,[] => []
  | .node lh::lt,.node rh::rt =>
    longer (level (.node lh::lt) (.node rh::rt))
      (longer (longer (anywhere lh (.node rh::rt)) (anywhere lt (.node rh::rt)))
        (longer (anywhere (.node lh::lt) rh) (anywhere (.node lh::lt) rt)))
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- Choosing a longer forest preserves independent common feasibility. -/
theorem longer_feasible {P : List OrderedTree → Prop} {first second : List OrderedTree}
    (hfirst : P first) (hsecond : P second) : P (longer first second) := by
  unfold longer
  split
  · exact hsecond
  · exact hfirst

/-- Every returned level witness is an ordered child selection in both inputs. -/
theorem level_sound (left right : List OrderedTree) :
    ForestPrunes (level left right) left ∧ ForestPrunes (level left right) right := by
  rw [level.eq_def]
  cases left with
  | nil => exact ⟨.nil _,.nil _⟩
  | cons first lt =>
    cases right with
    | nil => exact ⟨.nil _,.nil _⟩
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          dsimp only
          apply longer_feasible (P := fun candidate => ForestPrunes candidate (.node lh::lt) ∧ ForestPrunes candidate (.node rh::rt))
          · apply longer_feasible (P := fun candidate => ForestPrunes candidate (.node lh::lt) ∧ ForestPrunes candidate (.node rh::rt))
            · have hh := level_sound lh rh
              have ht := level_sound lt rt
              exact ⟨.cons (.node hh.1) ht.1,.cons (.node hh.2) ht.2⟩
            · have h := level_sound lt (.node rh::rt)
              exact ⟨.skip _ h.1,h.2⟩
          · have h := level_sound (.node lh::lt) rt
            exact ⟨h.1,.skip _ h.2⟩
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- Completeness: every independently selected common forest is bounded by
this separately computed level witness. -/
theorem level_upper (left right candidate : List OrderedTree)
    (hl : ForestPrunes candidate left) (hr : ForestPrunes candidate right) :
    forestEdgeCount candidate ≤ forestEdgeCount (level left right) := by
  cases left with
  | nil => rw [hl.eq_nil_of_nil]; simp only [forestEdgeCount_nil]; omega
  | cons first lt =>
    cases right with
    | nil => rw [hr.eq_nil_of_nil]; simp only [forestEdgeCount_nil]; omega
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          rw [level]
          simp only [longer_edges,forestEdgeCount_cons,edgeCount_node]
          cases candidate with
          | nil => simp only [forestEdgeCount_nil]; omega
          | cons child rest =>
            rcases hl.first with hd | ⟨hc,ht⟩
            · have hu := level_upper lt (.node rh::rt) (child::rest) hd hr
              omega
            · rcases hr.first with hd | ⟨hc',ht'⟩
              · have hu := level_upper (.node lh::lt) rt (child::rest) hl hd
                omega
              · cases child with
                | node inside =>
                  have hi := level_upper lh rh inside hc.children hc'.children
                  have ho := level_upper lt rt rest ht ht'
                  simp only [forestEdgeCount_cons,edgeCount_node]
                  omega
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- The returned general witness is a connected ordered subtree in both inputs,
with the chosen root allowed to differ from each original root. -/
theorem anywhere_sound (left right : List OrderedTree) :
    IsomorphicSubtree (.node (anywhere left right)) (.node left) ∧
      IsomorphicSubtree (.node (anywhere left right)) (.node right) := by
  rw [anywhere.eq_def]
  cases left with
  | nil => exact ⟨(RootPrunes.node (.nil _)).isomorphicSubtree,(RootPrunes.node (.nil _)).isomorphicSubtree⟩
  | cons first lt =>
    cases right with
    | nil => exact ⟨(RootPrunes.node (.nil _)).isomorphicSubtree,(RootPrunes.node (.nil _)).isomorphicSubtree⟩
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          dsimp only
          apply longer_feasible (P := fun candidate => IsomorphicSubtree (.node candidate) (.node (.node lh::lt)) ∧ IsomorphicSubtree (.node candidate) (.node (.node rh::rt)))
          · have h := level_sound (.node lh::lt) (.node rh::rt)
            exact ⟨(RootPrunes.node h.1).isomorphicSubtree,(RootPrunes.node h.2).isomorphicSubtree⟩
          · apply longer_feasible (P := fun candidate => IsomorphicSubtree (.node candidate) (.node (.node lh::lt)) ∧ IsomorphicSubtree (.node candidate) (.node (.node rh::rt)))
            · apply longer_feasible (P := fun candidate => IsomorphicSubtree (.node candidate) (.node (.node lh::lt)) ∧ IsomorphicSubtree (.node candidate) (.node (.node rh::rt)))
              · have h := anywhere_sound lh (.node rh::rt)
                exact ⟨h.1.below (by simp only [children,List.mem_cons]; exact Or.inl True.intro),h.2⟩
              · have h := anywhere_sound lt (.node rh::rt)
                exact ⟨h.1.skip,h.2⟩
            · apply longer_feasible (P := fun candidate => IsomorphicSubtree (.node candidate) (.node (.node lh::lt)) ∧ IsomorphicSubtree (.node candidate) (.node (.node rh::rt)))
              · have h := anywhere_sound (.node lh::lt) rh
                exact ⟨h.1,h.2.below (by simp only [children,List.mem_cons]; exact Or.inl True.intro)⟩
              · have h := anywhere_sound (.node lh::lt) rt
                exact ⟨h.1,h.2.skip⟩
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- Every independent common subtree is bounded, including roots below either
input root. No presumed recurrence optimum is used as a hypothesis. -/
theorem anywhere_upper (left right : List OrderedTree) (candidate : OrderedTree)
    (hl : IsomorphicSubtree candidate (.node left)) (hr : IsomorphicSubtree candidate (.node right)) :
    candidate.edgeCount ≤ forestEdgeCount (anywhere left right) := by
  cases left with
  | nil =>
    have hb := hl.edgeCount_le
    simp only [edgeCount_node,forestEdgeCount_nil] at hb
    omega
  | cons first lt =>
    cases right with
    | nil =>
      have hb := hr.edgeCount_le
      simp only [edgeCount_node,forestEdgeCount_nil] at hb
      omega
    | cons second rt =>
      cases first with
      | node lh =>
        cases second with
        | node rh =>
          rw [anywhere]
          simp only [longer_edges]
          rcases hl.first with hlroot | hlhead | hltail
          · rcases hr.first with hrroot | hrhead | hrtail
            · have hb := level_upper (.node lh::lt) (.node rh::rt) candidate.children hlroot.children hrroot.children
              cases candidate
              simp only [children,edgeCount_node] at *
              omega
            · have hb := anywhere_upper (.node lh::lt) rh candidate hl hrhead
              omega
            · have hb := anywhere_upper (.node lh::lt) rt candidate hl hrtail
              omega
          · have hb := anywhere_upper lh (.node rh::rt) candidate hlhead hr
            omega
          · have hb := anywhere_upper lt (.node rh::rt) candidate hltail hr
            omega
termination_by forestEdgeCount left + forestEdgeCount right
decreasing_by all_goals simp_all only [forestEdgeCount_cons,edgeCount_node]; omega

/-- Constructive independent optimum of the root-preserving state. -/
theorem level_correct (left right : OrderedTree) :
    IsMaximumRootedIsomorphism (.node (level left.children right.children)) left right := by
  cases left with
  | node ls =>
    cases right with
    | node rs =>
      have h := level_sound ls rs
      refine ⟨⟨.node h.1,.node h.2⟩,?_⟩
      intro other hl hr
      cases other with
      | node children => exact level_upper ls rs children hl.children hr.children

/-- Constructive independent maximum connected ordered subtree. -/
theorem anywhere_correct (left right : OrderedTree) :
    IsMaximumIsomorphism (.node (anywhere left.children right.children)) left right := by
  cases left with
  | node ls =>
    cases right with
    | node rs =>
      exact ⟨anywhere_sound ls rs,fun other hl hr => anywhere_upper ls rs other hl hr⟩

end OrderedIsoDP
end SubtreeProofs.Paper2004.OrderedTree

end
