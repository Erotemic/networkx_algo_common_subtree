module

public import SubtreeProofs.Rust.AssignmentAugmentation
import Mathlib.Tactic

/-!
# Combinatorics of the independent augmentation path

The path reroutes real columns bijectively onto all original columns except
its unmatched head, including the reserved column zero. These statements
concern only the input path and predecessor function.
-/

@[expose] public section

open Aeneas Aeneas.Std

namespace SubtreeProofs.Rust.AssignmentAugmentationPath

open AssignmentAugmentation

def route (predecessor : Slice Usize) (path : List Nat) (col : Nat) : Nat :=
  if col ∈ path then predecessor.val[col]!.val else col

theorem follows_map (predecessor : Slice Usize) (head : Nat) (rest : List Nat)
    (hfollow : Follows predecessor (head::rest)) :
    (head::rest).map (fun col => predecessor.val[col]!.val) = rest++[0] := by
  induction rest generalizing head with
  | nil => simpa only [List.map_cons, List.map_nil, List.nil_append, List.headD_nil] using congrArg (fun col => [col]) hfollow.1
  | cons next tail ih =>
    change predecessor.val[head]!.val :: (next::tail).map (fun col => predecessor.val[col]!.val) = (next::tail)++[0]
    rw [show predecessor.val[head]!.val = next from hfollow.1, ih next hfollow.2]
    rfl

theorem zero_not_mem (predecessor : Slice Usize) (n : Usize) (path : List Nat)
    (hvalid : ValidPath predecessor n path) : 0 ∉ path := by
  intro hm
  exact (Nat.lt_irrefl 0) (hvalid.2.1 0 hm).1

theorem predecessor_mem (predecessor : Slice Usize) (head : Nat) (rest : List Nat) (index : Nat)
    (hfollow : Follows predecessor (head::rest)) :
    (∃ col ∈ head::rest, predecessor.val[col]!.val = index) ↔ index ∈ rest ∨ index = 0 := by
  have hm : (∃ col ∈ head::rest, predecessor.val[col]!.val = index) ↔
      index ∈ (head::rest).map (fun col => predecessor.val[col]!.val) := List.mem_map.symm
  rw [hm, follows_map predecessor head rest hfollow]
  simp only [List.mem_append, List.mem_singleton]

theorem predecessor_injective (predecessor : Slice Usize) (n : Usize) (head : Nat) (rest : List Nat)
    (hvalid : ValidPath predecessor n (head::rest)) :
    Set.InjOn (fun (col : Nat) => predecessor.val[col]!.val) ((head::rest).toFinset : Set Nat) := by
  have hz : 0 ∉ rest := fun hm => zero_not_mem predecessor n (head::rest) hvalid (List.mem_cons_of_mem head hm)
  have hnd : (rest++[0]).Nodup := by
    apply List.nodup_append.mpr
    refine ⟨(List.nodup_cons.mp hvalid.1).2,by simp,?_⟩
    intro first hf second hs he
    have hs0 : second = 0 := List.mem_singleton.mp hs
    exact hz (he.trans hs0 ▸ hf)
  have hmap : ((head::rest).map (fun col => predecessor.val[col]!.val)).Nodup := by
    rw [follows_map predecessor head rest hvalid.2.2]
    exact hnd
  have hi := (List.nodup_map_iff_inj_on hvalid.1).mp hmap
  intro first hf second hs he
  exact hi first (List.mem_toFinset.mp hf) second (List.mem_toFinset.mp hs) he

theorem route_bound (predecessor : Slice Usize) (n : Usize) (head : Nat) (rest : List Nat)
    (hvalid : ValidPath predecessor n (head::rest)) (col : Nat) (hc : 0 < col) (hle : col ≤ n.val) :
    route predecessor (head::rest) col ≤ n.val ∧ route predecessor (head::rest) col ≠ head := by
  by_cases hm : col ∈ head::rest
  · simp only [route, hm, ↓reduceIte]
    have hnext := (predecessor_mem predecessor head rest _ hvalid.2.2).mp ⟨col,hm,rfl⟩
    rcases hnext with ht | hz
    · have hb := hvalid.2.1 _ (List.mem_cons_of_mem head ht)
      refine ⟨hb.2,?_⟩
      intro he
      exact (List.nodup_cons.mp hvalid.1).1 (he ▸ ht)
    · have hhead := (hvalid.2.1 head (by simp)).1
      exact ⟨by omega,by omega⟩
  · simp only [route,hm,↓reduceIte]
    exact ⟨hle,fun he => hm (he ▸ List.mem_cons_self)⟩

theorem route_injective (predecessor : Slice Usize) (n : Usize) (head : Nat) (rest : List Nat)
    (hvalid : ValidPath predecessor n (head::rest)) :
    Set.InjOn (route predecessor (head::rest)) (Finset.Icc 1 n.val) := by
  intro first hf second hs he
  have hfirst := Finset.mem_Icc.mp hf
  have hsecond := Finset.mem_Icc.mp hs
  by_cases hm : first ∈ head::rest <;> by_cases hn : second ∈ head::rest
  · simp only [route,hm,hn,↓reduceIte] at he
    exact predecessor_injective predecessor n head rest hvalid
      (List.mem_toFinset.mpr hm) (List.mem_toFinset.mpr hn) he
  · simp only [route,hm,hn,↓reduceIte] at he
    have hnext := (predecessor_mem predecessor head rest second hvalid.2.2).mp ⟨first,hm,he⟩
    rcases hnext with ht | hz
    · exact False.elim (hn (List.mem_cons_of_mem head ht))
    · omega
  · simp only [route,hm,hn,↓reduceIte] at he
    have hnext := (predecessor_mem predecessor head rest first hvalid.2.2).mp ⟨second,hn,he.symm⟩
    rcases hnext with ht | hz
    · exact False.elim (hm (List.mem_cons_of_mem head ht))
    · omega
  · simpa only [route,hm,hn,↓reduceIte] using he

theorem route_surjective (predecessor : Slice Usize) (n : Usize) (head : Nat) (rest : List Nat)
    (hvalid : ValidPath predecessor n (head::rest)) (original : Nat)
    (hle : original ≤ n.val) (hne : original ≠ head) :
    ∃ col, 0 < col ∧ col ≤ n.val ∧ route predecessor (head::rest) col = original := by
  by_cases hm : original ∈ rest ∨ original = 0
  · obtain ⟨col,hcol,he⟩ := (predecessor_mem predecessor head rest original hvalid.2.2).mpr hm
    have hb := hvalid.2.1 col hcol
    exact ⟨col,hb.1,hb.2,by simpa only [route,hcol,↓reduceIte] using he⟩
  · have hnot : original ∉ head::rest := by
      simp only [List.mem_cons]
      exact fun he => he.elim hne (fun ht => hm (Or.inl ht))
    exact ⟨original,by omega,hle,by simp only [route,hnot,↓reduceIte]⟩

end SubtreeProofs.Rust.AssignmentAugmentationPath

end
