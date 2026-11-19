module

public import SubtreeProofs.Rust.AssignmentPredecessorPaths
public import SubtreeProofs.Rust.AssignmentSearchCapacity
public import SubtreeProofs.Rust.AssignmentScanCut
import Mathlib.Tactic

/-!
# Discovery ranks for the actual alternating-tree search

Visited vertices retain their discovery ranks; unvisited vertices share the
current visit count. Visiting a pending vertex and updating that common rank
preserves strict predecessor descent. The actual scan leaves used-column
predecessors untouched, while its selected unused column points into the
visited set and therefore extends a finite ranked forest.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentDiscoveryRanks

open AssignmentScanInvariant AssignmentAdjustmentInvariant AssignmentPredecessorPaths

def DiscoveryBound (used : Finset Nat) (rank : Nat → Nat) (visited : Nat) : Prop :=
  (∀ col ∈ used, rank col < visited) ∧ ∀ col, col ∉ used → rank col = visited

def advanceRank (used : Finset Nat) (rank : Nat → Nat) (visited : Nat) (col : Nat) : Nat :=
  if col ∈ used then rank col else visited

theorem discovery_initial : DiscoveryBound ∅ (fun _ => 0) 0 := by simp [DiscoveryBound]

theorem discovery_visit (used : Finset Nat) (rank : Nat → Nat) (visited column : Nat)
    (hbound : DiscoveryBound used rank visited) (hnew : column ∉ used) :
    DiscoveryBound (insert column used) (advanceRank (insert column used) rank (visited+1)) (visited+1) := by
  constructor
  · intro col hc
    simp only [advanceRank,hc,↓reduceIte]
    rcases Finset.mem_insert.mp hc with he | hm
    · subst col
      rw [hbound.2 column hnew]
      omega
    · exact Nat.lt_succ_of_lt (hbound.1 col hm)
  · intro col hc
    simp only [advanceRank,hc,↓reduceIte]

theorem ranked_visit (predecessor : Slice Usize) (n : Usize) (used : Finset Nat) (rank : Nat → Nat)
    (visited column : Nat) (hforest : Ranked predecessor n used rank)
    (hbound : DiscoveryBound used rank visited) (hcolumn : column ≤ n.val) (hnew : column ∉ used)
    (hpending : column ≠ 0 → predecessor.val[column]!.val ∈ used) :
    Ranked predecessor n (insert column used) (advanceRank (insert column used) rank (visited+1)) := by
  refine ⟨?_,?_⟩
  · intro col hc
    rcases Finset.mem_insert.mp hc with he | hm
    · simpa only [he] using hcolumn
    · exact hforest.1 col hm
  · intro col hc hz
    rcases Finset.mem_insert.mp hc with he | hm
    · subst col
      have hp := hpending hz
      have hpi : predecessor.val[column]!.val ∈ insert column used := Finset.mem_insert_of_mem hp
      refine ⟨hpi,?_⟩
      simp only [advanceRank,hpi,Finset.mem_insert_self,↓reduceIte]
      rw [hbound.2 column hnew]
      exact hbound.1 _ hp
    · obtain ⟨hp,hr⟩ := hforest.2 col hm hz
      have hpi : predecessor.val[col]!.val ∈ insert column used := Finset.mem_insert_of_mem hp
      have hci : col ∈ insert column used := Finset.mem_insert_of_mem hm
      exact ⟨hpi,by simpa only [advanceRank,hpi,hci,↓reduceIte] using hr⟩

/-- An unused selected column whose predecessor is visited extends the
ranked forest, including when it is the unmatched terminal returned to the
augmentation phase. -/
theorem ranked_terminal (predecessor : Slice Usize) (n : Usize) (used : Finset Nat) (rank : Nat → Nat)
    (visited column : Nat) (hforest : Ranked predecessor n used rank)
    (hbound : DiscoveryBound used rank visited) (hcolumn : column ≤ n.val) (hnew : column ∉ used)
    (hprevious : predecessor.val[column]!.val ∈ used) : Ranked predecessor n (insert column used) rank := by
  refine ⟨?_,?_⟩
  · intro col hc
    rcases Finset.mem_insert.mp hc with he | hm
    · simpa only [he] using hcolumn
    · exact hforest.1 col hm
  · intro col hc hz
    rcases Finset.mem_insert.mp hc with he | hm
    · subst col
      refine ⟨Finset.mem_insert_of_mem hprevious,?_⟩
      rw [hbound.2 column hnew]
      exact hbound.1 _ hprevious
    · obtain ⟨hp,hr⟩ := hforest.2 col hm hz
      exact ⟨Finset.mem_insert_of_mem hp,hr⟩

theorem ranked_congr (before after : Slice Usize) (n : Usize) (used : Finset Nat) (rank : Nat → Nat)
    (hforest : Ranked before n used rank) (heq : ∀ col ∈ used, before.val[col]!.val = after.val[col]!.val) :
    Ranked after n used rank := by
  refine ⟨hforest.1,?_⟩
  intro col hc hz
  rw [← heq col hc]
  exact hforest.2 col hc hz

/-- Used-column slots are physically unchanged by the actual complete scan. -/
theorem scan_predecessor_unchanged (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (slack : alloc.vec.Vec (Option I128)) (predecessor newPred : alloc.vec.Vec Usize) (column n : Usize)
    (hplen : n.val < predecessor.length)
    (hframe : PredecessorPrefix used weights slack predecessor newPred column (n.val+1))
    (col : Nat) (hc : col ∈ usedIndices used (n.val+1)) : newPred.val[col]! = predecessor.val[col]! := by
  have hm := (mem_usedIndices used _ _).mp hc
  have hb : col < predecessor.length := by omega
  have hnot : col ∉ selectedPrefix used (n.val+1) := by
    intro hs
    have hh := (mem_selectedPrefix used _ _).mp hs
    rw [hm.2] at hh
    exact Bool.noConfusion hh.2.2
  simpa only [hnot,false_and,↓reduceIte] using hframe.2 col hb

/-- The exact table frame proved for the actual scan preserves all predecessor
links of the already visited forest, including zero's unused slot. -/
theorem scan_preserves_forest (used : Slice Bool) (weights : Nat → WithTop ℤ)
    (slack : alloc.vec.Vec (Option I128)) (predecessor newPred : alloc.vec.Vec Usize) (column n : Usize)
    (rank : Nat → Nat) (hplen : n.val < predecessor.length)
    (hforest : Ranked (alloc.vec.Vec.deref predecessor) n (usedIndices used (n.val+1)) rank)
    (hframe : PredecessorPrefix used weights slack predecessor newPred column (n.val+1)) :
    Ranked (alloc.vec.Vec.deref newPred) n (usedIndices used (n.val+1)) rank := by
  apply ranked_congr (alloc.vec.Vec.deref predecessor) (alloc.vec.Vec.deref newPred) n _ rank hforest
  intro col hc
  have he := scan_predecessor_unchanged used weights slack predecessor newPred column n hplen hframe col hc
  simpa only [alloc.vec.Vec.deref,Slice.from_val] using (congrArg UScalar.val he).symm

end SubtreeProofs.Rust.AssignmentDiscoveryRanks

end
