module

public import SubtreeProofs.Shared.CopiedMatchingDeletion
import Mathlib.Tactic

/-!
# Initial dual and larger-side tight matching of 2016 Lemma 5

Each left vertex and its copy receive their row's maximum nonnegative weight.
Each right vertex and its copy receive zero. The right identity-copy edges
form a compatible tight matching of cardinality |R|, so exactly |L| edges are
missing from a perfect assignment. The maximum includes zero explicitly,
covering absent/empty rows without an undefined maximum of an empty set.
-/

@[expose] public section

namespace SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

variable {L R K : Type*} [Fintype L] [Fintype R] [DecidableEq L] [DecidableEq R]
  [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

noncomputable def rowChoices (weights : L → R → Option K) (left : L) : Finset K := by
  classical
  exact insert 0 (Finset.univ.image (fun right => (weights left right).getD 0))

theorem rowChoices_nonempty (weights : L → R → Option K) (left : L) : (rowChoices weights left).Nonempty := by
  classical
  exact Finset.insert_nonempty _ _

/-- Exact source row maximum, with zero for an absent/nonpositive row. -/
noncomputable def rowMaximum (weights : L → R → Option K) (left : L) : K :=
  (rowChoices weights left).max' (rowChoices_nonempty weights left)

theorem rowMaximum_nonnegative (weights : L → R → Option K) (left : L) : 0 ≤ rowMaximum weights left := by
  classical
  exact Finset.le_max' _ 0 (Finset.mem_insert_self _ _)

theorem entry_le_rowMaximum (weights : L → R → Option K) (left : L) (right : R) :
    (weights left right).getD 0 ≤ rowMaximum weights left := by
  classical
  apply Finset.le_max'
  exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨right,Finset.mem_univ _,rfl⟩)

/-- The chosen potential is the least bound on zero and all row entries. -/
theorem rowMaximum_le (weights : L → R → Option K) (left : L) (upper : K)
    (hzero : 0 ≤ upper) (hentries : ∀ right, (weights left right).getD 0 ≤ upper) :
    rowMaximum weights left ≤ upper := by
  classical
  apply Finset.max'_le
  intro value hv
  simp only [rowChoices,Finset.mem_insert,Finset.mem_image,Finset.mem_univ,true_and] at hv
  rcases hv with rfl | ⟨right,rfl⟩
  · exact hzero
  · exact hentries right

noncomputable def initialPotential (weights : L → R → Option K) : L ⊕ R → K
  | .inl left => rowMaximum weights left
  | .inr _ => 0

/-- Maximization dual convention used by the paper, on actual allowed edges. -/
def DualFeasible (weights : L → R → Option K) (rows columns : L ⊕ R → K) : Prop :=
  ∀ row column, Allowed weights row column → profit weights row column ≤ rows row + columns column

/-- The exact initial potentials are feasible on the copied graph. This proof
also bounds zero-valued absent pairs, without making them source edges. -/
theorem initial_dual_feasible (weights : L → R → Option K) :
    DualFeasible weights (initialPotential weights) (initialPotential weights) := by
  intro row column _
  cases row with
  | inl left =>
    cases column with
    | inl other =>
      simp only [profit,AssignmentReduction.profit,add_zero,initialPotential]
      exact add_nonneg (rowMaximum_nonnegative weights left) (rowMaximum_nonnegative weights other)
    | inr right =>
      simp only [profit,AssignmentReduction.profit,add_zero,initialPotential]
      exact max_le (rowMaximum_nonnegative weights left) (entry_le_rowMaximum weights left right)
  | inr right =>
    cases column with
    | inl left =>
      simp only [profit,AssignmentReduction.profit,zero_add,initialPotential]
      exact max_le (rowMaximum_nonnegative weights left) (entry_le_rowMaximum weights left right)
    | inr other => simp only [profit,AssignmentReduction.profit,initialPotential,add_zero,le_refl]

/-- Right vertices are initially paired to their own copies. -/
def initialPairs : Finset ((L ⊕ R) × (L ⊕ R)) :=
  (Finset.univ : Finset R).image (fun right => (Sum.inr right,Sum.inr right))

@[simp] theorem mem_initialPairs (pair : (L ⊕ R) × (L ⊕ R)) :
    pair ∈ (initialPairs : Finset ((L ⊕ R) × (L ⊕ R))) ↔ ∃ right, pair = (Sum.inr right,Sum.inr right) := by
  simp only [initialPairs,Finset.mem_image,Finset.mem_univ,true_and]
  constructor <;> rintro ⟨right,he⟩ <;> exact ⟨right,he.symm⟩

theorem initialPairs_valid (weights : L → R → Option K) : Valid (edgeWeight weights) initialPairs := by
  refine ⟨?_,?_,?_⟩
  · intro pair hp
    obtain ⟨right,rfl⟩ := (mem_initialPairs pair).mp hp
    simp only [identity_edge_weight,ne_eq,reduceCtorEq,not_false_eq_true]
  · intro pair hp other ho he
    obtain ⟨right,rfl⟩ := (mem_initialPairs pair).mp hp
    obtain ⟨target,rfl⟩ := (mem_initialPairs other).mp ho
    exact Prod.ext he he
  · intro pair hp other ho he
    obtain ⟨right,rfl⟩ := (mem_initialPairs pair).mp hp
    obtain ⟨target,rfl⟩ := (mem_initialPairs other).mp ho
    exact Prod.ext he he

theorem initialPairs_card : (initialPairs : Finset ((L ⊕ R) × (L ⊕ R))).card = Fintype.card R := by
  rw [initialPairs,Finset.card_image_iff.mpr]
  · exact Finset.card_univ
  · intro first _ second _ he
    exact Sum.inr.inj (congrArg Prod.fst he)

/-- Every edge of the actual larger-side initial matching is tight under the
exact source potential, independently of any later optimal matching result. -/
theorem initialPairs_tight (weights : L → R → Option K) :
    ∀ pair ∈ initialPairs, initialPotential weights pair.1 + initialPotential weights pair.2 = profit weights pair.1 pair.2 := by
  intro pair hp
  obtain ⟨right,rfl⟩ := (mem_initialPairs pair).mp hp
  simp only [initialPotential,profit,AssignmentReduction.profit,add_zero]

/-- When |L| ≤ |R|, this is precisely the source's |L| initial edge deficit. -/
theorem initial_edge_deficit : Fintype.card L + Fintype.card R - (initialPairs : Finset ((L ⊕ R) × (L ⊕ R))).card = Fintype.card L := by
  rw [initialPairs_card]
  omega

/-- Feasible dual values restrict to the induced surviving graph unchanged;
removed endpoints introduce no additional allowed-edge obligations. -/
theorem deletion_preserves_dual_feasible (weights : L → R → Option K) (rows columns : L ⊕ R → K)
    (h : DualFeasible weights rows columns) (removed : R) :
    ∀ row column : {vertex : L ⊕ R // vertex ≠ Sum.inr removed},
      Allowed weights row.val column.val → profit weights row.val column.val ≤ rows row.val + columns column.val := by
  exact fun row column he => h row.val column.val he

end SubtreeProofs.WeightedMatching.CopiedAssignmentReduction

end
