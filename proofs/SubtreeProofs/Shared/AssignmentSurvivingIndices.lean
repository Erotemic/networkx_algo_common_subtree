module

public import SubtreeProofs.Shared.AssignmentFiniteDeletion
public import Mathlib.Data.List.Sort
import Mathlib.Tactic

/-! # Increasing surviving-index lists equal the canonical finite enumeration -/

@[expose] public section

namespace SubtreeProofs.AssignmentVertexDeletion

def survivingIndices (extent removed : Nat) : List Nat :=
  (List.range extent).filter (fun vertex => vertex != removed)

theorem survivingIndices_succ (extent removed : Nat) :
    survivingIndices (extent+1) removed =
      if extent = removed then survivingIndices extent removed else survivingIndices extent removed ++ [extent] := by
  unfold survivingIndices
  rw [List.range_succ,List.filter_append]
  by_cases he : extent = removed
  · simp only [he,bne_self_eq_false,List.filter_cons,List.filter_nil,Bool.false_eq_true,↓reduceIte,List.append_nil]
  · have hb : (extent != removed) = true := bne_iff_ne.mpr he
    simp only [he,hb,List.filter_cons,List.filter_nil,↓reduceIte]

theorem survivingIndices_canonical {n : Nat} (removed : Fin (n+1)) :
    survivingIndices (n+1) removed.val = (List.finRange n).map (fun vertex => (removed.succAbove vertex).val) := by
  have hLeft : (survivingIndices (n+1) removed.val).Pairwise (· < ·) :=
    List.pairwise_lt_range.filter _
  have hRight : ((List.finRange n).map (fun vertex => (removed.succAbove vertex).val)).Pairwise (· < ·) := by
    apply List.pairwise_map.mpr
    apply (List.sortedLT_finRange n).pairwise.imp
    intro first second hlt
    change (remainingEquiv removed first).val.val < (remainingEquiv removed second).val.val
    rw [remainingEquiv_val,remainingEquiv_val]
    have hv : first.val < second.val := hlt
    split <;> split <;> omega
  apply hLeft.eq_of_mem_iff hRight
  intro value
  simp only [survivingIndices,List.mem_filter,List.mem_range,bne_iff_ne,List.mem_map]
  constructor
  · rintro ⟨hBound,hNe⟩
    have hn : (⟨value,hBound⟩ : Fin (n+1)) ≠ removed := fun he => hNe (congrArg Fin.val he)
    obtain ⟨vertex,hVertex⟩ := Fin.exists_succAbove_eq hn
    exact ⟨vertex,List.mem_finRange vertex,congrArg Fin.val hVertex⟩
  · rintro ⟨vertex,_,he⟩
    subst value
    refine ⟨(removed.succAbove vertex).isLt,?_⟩
    intro hh
    exact Fin.succAbove_ne removed vertex (Fin.ext hh)

end SubtreeProofs.AssignmentVertexDeletion

end
