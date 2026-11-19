module

public import SubtreeProofs.Shared.WeightedMatching
public import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-!
# Matching reuse under vertex deletion

Delete a right vertex by forbidding every incident pair, retaining its original
index. Independent feasibility and scores agree with the induced smaller graph.
An existing maximum remains maximum when the deleted vertex is unmatched.
Only matched right vertices can require a new solution; their count is the
matching cardinality and is bounded by the smaller bipartition size.

These are the reuse and counting steps in Droschinsky et al. 2016 Lemma 6.
One-augmentation repair, the source implementation and the advertised running
time are separate obligations.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching

variable {L R W : Type*} [DecidableEq L] [DecidableEq R]
  [AddCommMonoid W] [LinearOrder W]

/-- Vertex deletion with surviving vertices retaining their original indices. -/
def deleteRight (weights : L → R → Option W) (removed : R) : L → R → Option W :=
  fun left right => if right = removed then none else weights left right

/-- Right endpoints used by a matching; independent of how it was computed. -/
def matchedRight (pairs : Finset (L × R)) : Finset R := pairs.image Prod.snd

/-- The corresponding left endpoint set. -/
def matchedLeft (pairs : Finset (L × R)) : Finset L := pairs.image Prod.fst

theorem valid_deleteRight_iff (weights : L → R → Option W) (removed : R) (pairs : Finset (L × R)) :
    Valid (deleteRight weights removed) pairs ↔ Valid weights pairs ∧ removed ∉ matchedRight pairs := by
  constructor
  · intro h
    have havoid : ∀ p ∈ pairs, p.2 ≠ removed := by
      intro p hp he
      have hh := h.1 p hp
      simp only [deleteRight,he,↓reduceIte,ne_eq,not_true_eq_false] at hh
    refine ⟨⟨?_,h.2⟩,?_⟩
    · intro p hp
      simpa only [deleteRight,havoid p hp,↓reduceIte] using h.1 p hp
    · intro hm
      obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hm
      exact havoid p hp he
  · rintro ⟨h,havoid⟩
    refine ⟨?_,h.2⟩
    intro p hp
    have hn : p.2 ≠ removed := by
      intro he
      apply havoid
      exact Finset.mem_image.mpr ⟨p,hp,he⟩
    simpa only [deleteRight,hn,↓reduceIte] using h.1 p hp

/-- Deleting an unused vertex preserves the exact score of every surviving
matching, including signed and forbidden weights. -/
theorem weight_deleteRight (weights : L → R → Option W) (removed : R) (pairs : Finset (L × R))
    (havoid : removed ∉ matchedRight pairs) :
    weight (deleteRight weights removed) pairs = weight weights pairs := by
  apply Finset.sum_congr rfl
  intro p hp
  have hn : p.2 ≠ removed := by
    intro he
    exact havoid (Finset.mem_image.mpr ⟨p,hp,he⟩)
  simp only [deleteRight,hn,↓reduceIte]

/-- The unmatched-vertex branch of 2016 Lemma 6: reuse the actual previous
optimum, with no new matching computation or supplied deletion optimum. -/
theorem IsMaximum.deleteRight {weights : L → R → Option W} {pairs : Finset (L × R)}
    (h : IsMaximum weights pairs) (removed : R) (havoid : removed ∉ matchedRight pairs) :
    IsMaximum (deleteRight weights removed) pairs := by
  refine ⟨(valid_deleteRight_iff weights removed pairs).mpr ⟨h.1,havoid⟩,?_⟩
  intro other hother
  have ho := (valid_deleteRight_iff weights removed other).mp hother
  rw [weight_deleteRight weights removed other ho.2,weight_deleteRight weights removed pairs havoid]
  exact h.2 other ho.1

/-- Projection is injective on feasible pairs, so the number of used right
vertices is exactly the number of matching edges. -/
theorem matchedRight_card {weights : L → R → Option W} {pairs : Finset (L × R)} (h : Valid weights pairs) :
    (matchedRight pairs).card = pairs.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  exact h.2.2 p hp q hq he

theorem matchedLeft_card {weights : L → R → Option W} {pairs : Finset (L × R)} (h : Valid weights pairs) :
    (matchedLeft pairs).card = pairs.card := by
  apply Finset.card_image_iff.mpr
  intro p hp q hq he
  exact h.2.1 p hp q hq he

/-- At most the smaller side's size requires deletion repair, even when every
right vertex is queried. This counts potential repairs, not their runtime. -/
theorem deletion_repair_card_bound [Fintype L] [Fintype R]
    {weights : L → R → Option W} {pairs : Finset (L × R)} (h : Valid weights pairs) :
    (matchedRight pairs).card ≤ min (Fintype.card L) (Fintype.card R) := by
  apply le_min
  · rw [matchedRight_card h,← matchedLeft_card h]
    exact Finset.card_le_univ _
  · exact Finset.card_le_univ _

/-- A reference deletion family, reusing the original optimum whenever it
survives and otherwise invoking the existing independent exhaustive solver. -/
def deletionFamily (left right : Nat) (weights : Fin left → Fin right → Option W)
    (original : Finset (Fin left × Fin right)) (removed : Fin right) : Finset (Fin left × Fin right) :=
  if removed ∈ matchedRight original then solveMatrix left right (deleteRight weights removed) else original

/-- Every family member is independently optimal for its own deleted instance. -/
theorem deletionFamily_correct (left right : Nat) (weights : Fin left → Fin right → Option W)
    (original : Finset (Fin left × Fin right)) (h : IsMaximum weights original) (removed : Fin right) :
    IsMaximum (deleteRight weights removed) (deletionFamily left right weights original removed) := by
  unfold deletionFamily
  split
  · exact solveMatrix_correct _ _ _
  · rename_i hn
    exact h.deleteRight removed hn

end SubtreeProofs.WeightedMatching

end
