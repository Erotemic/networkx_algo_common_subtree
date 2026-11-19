module

public import Mathlib.Data.Finset.Lattice.Fold
public import Mathlib.Order.WithBot
public import Mathlib.Algebra.Order.Monoid.Unbundled.WithTop
import Mathlib.Tactic

/-!
# Independent attained minima for Hungarian slack tables

An absent slack is positive infinity. Finite slacks have an attaining
predecessor among the candidate columns, and are lower bounds for every
candidate's reduced cost. Candidate insertion retains the first predecessor
on ties. Uniform cut adjustment subtracts the same finite amount from all
candidate costs and the stored minimum.
-/

@[expose] public section

namespace SubtreeProofs.Assignment

structure MinimumAt (weights : Nat → ℤ) (candidates : Finset Nat) (slack : WithTop ℤ) (predecessor : Nat) : Prop where
  lower : ∀ candidate ∈ candidates, slack ≤ (weights candidate : WithTop ℤ)
  attained : slack ≠ ⊤ → predecessor ∈ candidates ∧ slack = (weights predecessor : WithTop ℤ)

theorem minimumAt_empty (weights : Nat → ℤ) (predecessor : Nat) : MinimumAt weights ∅ ⊤ predecessor := by
  exact ⟨by simp,by simp⟩

/-- Extending the candidate set takes the minimum and updates the predecessor
precisely on strict improvement, preserving an earlier predecessor on ties. -/
theorem MinimumAt.insert {weights : Nat → ℤ} {candidates : Finset Nat} {slack : WithTop ℤ} {predecessor : Nat}
    (h : MinimumAt weights candidates slack predecessor) (candidate : Nat) :
    MinimumAt weights (insert candidate candidates) (min slack (weights candidate : WithTop ℤ))
      (if (weights candidate : WithTop ℤ) < slack then candidate else predecessor) := by
  refine ⟨?_,?_⟩
  · intro other hm
    rcases Finset.mem_insert.mp hm with he | ho
    · subst other
      exact min_le_right _ _
    · exact (min_le_left _ _).trans (h.lower other ho)
  · intro _
    by_cases hi : (weights candidate : WithTop ℤ) < slack
    · simp only [hi,↓reduceIte]
      exact ⟨Finset.mem_insert_self _ _,min_eq_right (le_of_lt hi)⟩
    · have hle : slack ≤ (weights candidate : WithTop ℤ) := le_of_not_gt hi
      have hn : slack ≠ ⊤ := ne_top_of_le_ne_top (by simp) hle
      have ha := h.attained hn
      simp only [hi,↓reduceIte]
      exact ⟨Finset.mem_insert_of_mem ha.1,(min_eq_left hle).trans ha.2⟩

/-- A finite adjustment translates the independently specified attained
minimum and every candidate cost by exactly the same integer. -/
theorem MinimumAt.subtract {weights : Nat → ℤ} {candidates : Finset Nat} {slack : WithTop ℤ} {predecessor : Nat}
    (h : MinimumAt weights candidates slack predecessor) (amount : ℤ) :
    MinimumAt (fun candidate => weights candidate-amount) candidates
      (slack + ((-amount : ℤ) : WithTop ℤ)) predecessor := by
  refine ⟨?_,?_⟩
  · intro candidate hc
    have hb := add_le_add_right (h.lower candidate hc) ((-amount : ℤ) : WithTop ℤ)
    simpa only [← WithTop.coe_add,sub_eq_add_neg,add_comm] using hb
  · intro hn
    have hs : slack ≠ ⊤ := by intro he; exact hn (by rw [he,WithTop.top_add])
    obtain ⟨hc,he⟩ := h.attained hs
    refine ⟨hc,?_⟩
    rw [he,← WithTop.coe_add,sub_eq_add_neg]


/-- Only candidate costs matter to the attained minimum specification. -/
theorem MinimumAt.congr {weights other : Nat → ℤ} {candidates : Finset Nat} {slack : WithTop ℤ} {predecessor : Nat}
    (h : MinimumAt weights candidates slack predecessor)
    (heq : ∀ candidate ∈ candidates, weights candidate = other candidate) :
    MinimumAt other candidates slack predecessor := by
  refine ⟨?_,?_⟩
  · intro candidate hc
    rw [← heq candidate hc]
    exact h.lower candidate hc
  · intro hn
    obtain ⟨hc,he⟩ := h.attained hn
    exact ⟨hc,he.trans (congrArg (fun value : ℤ => (value : WithTop ℤ)) (heq predecessor hc))⟩

end SubtreeProofs.Assignment

end
