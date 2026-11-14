module

public import SubtreeProofs.Rust.Generated.VerifiedOrderedCore
public import SubtreeProofs.Paper2004.OrderedTree

/-!
# Refinement of the translated Rust contraction budget

The imported operation is generated from maintained Rust source. The final
lemma relates its returned machine integer to the independent tree relation.
-/

@[expose] public section

open Aeneas Aeneas.Std Result

namespace SubtreeProofs.Rust

/-- Zero edges is an ordinary documented rejection, not arithmetic failure. -/
theorem contractionBudget_zero :
    verified_ordered_core.remaining_edges_after_contraction 0#u32 = .ok none := by
  simp [verified_ordered_core.remaining_edges_after_contraction]

/-- On every positive input, translated Rust succeeds and removes one edge. -/
theorem contractionBudget_positive (edges : U32) (h : 0 < edges.val) :
    ∃ remaining, verified_ordered_core.remaining_edges_after_contraction edges = .ok (some remaining) ∧
      remaining.val + 1 = edges.val := by
  unfold verified_ordered_core.remaining_edges_after_contraction
  have hne : edges ≠ 0#u32 := by scalar_tac
  simp only [hne, ↓reduceIte]
  change ∃ remaining,
    Std.bind (UScalar.sub edges 1#u32) (fun i => ok (some i)) = ok (some remaining) ∧
      remaining.val + 1 = edges.val
  have hlt : ¬ edges.val < (1#u32).val := by scalar_tac
  simp only [UScalar.sub, hlt, ↓reduceIte, bind_ok]
  refine ⟨_, rfl, ?_⟩
  change ((edges.val - 1) % 2^32) + 1 = edges.val
  have hbound := edges.hBounds
  rw [Nat.mod_eq_of_lt (by simpa using (show edges.val - 1 < 2^32 by scalar_tac))]
  omega

/-- A real tree contraction refines the translated Rust budget operation.
The representation hypothesis bounds the mathematical edge count by `u32`. -/
theorem contractionBudget_refines_tree
    {before after : Paper2004.OrderedTree}
    (step : Paper2004.OrderedTree.ContractStep before after)
    (edges : U32) (represents : edges.val = before.edgeCount) :
    ∃ remaining, verified_ordered_core.remaining_edges_after_contraction edges = .ok (some remaining) ∧
      remaining.val = after.edgeCount := by
  have hdrop := step.edgeCount_decreases
  obtain ⟨remaining, hrun, hval⟩ := contractionBudget_positive edges (by omega)
  exact ⟨remaining, hrun, by omega⟩

end SubtreeProofs.Rust

end
