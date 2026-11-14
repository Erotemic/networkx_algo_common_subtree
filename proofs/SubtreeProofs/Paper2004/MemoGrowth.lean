module

public import SubtreeProofs.Paper2004.MemoizedDynamicProgram
import Mathlib.Tactic

/-! # Composable memo growth across multiple decomposition query families -/

@[expose] public section

namespace SubtreeProofs.Paper2004.OrderedTree

/-- A query sequence adds only keys in its permitted domain and preserves key
uniqueness. Existing table entries can come from earlier query families. -/
structure MemoGrowth (domain : MemoKey → Prop) (before after : MemoTable) : Prop where
  new_keys : ∀ entry ∈ after, entry ∈ before ∨ domain entry.1
  nodup : (before.map Prod.fst).Nodup → (after.map Prod.fst).Nodup

/-- No computation adds no keys. -/
theorem MemoGrowth.refl (domain : MemoKey → Prop) (table : MemoTable) : MemoGrowth domain table table :=
  ⟨fun _ he => Or.inl he,fun hn => hn⟩

/-- A larger finite query domain still covers all actual new keys. -/
theorem MemoGrowth.mono {first second : MemoKey → Prop} {before after : MemoTable}
    (h : MemoGrowth first before after) (hs : ∀ key, first key → second key) : MemoGrowth second before after :=
  ⟨fun entry he => (h.new_keys entry he).imp_right (hs entry.1),h.nodup⟩

/-- Sequential computations in one shared table add keys in the union of their
query families and continue to preserve actual uniqueness. -/
theorem MemoGrowth.trans {domain : MemoKey → Prop} {before middle after : MemoTable}
    (first : MemoGrowth domain before middle) (second : MemoGrowth domain middle after) : MemoGrowth domain before after := by
  refine ⟨?_,fun hn => second.nodup (first.nodup hn)⟩
  intro entry he
  rcases second.new_keys entry he with hm | hd
  · exact first.new_keys entry hm
  · exact Or.inr hd

/-- Every actual memo recurrence call obeys this composable growth invariant. -/
theorem memoLcs_growth (left right : DyckWord) (table : MemoTable) :
    MemoGrowth (MemoDomain left right) table (memoLcs left right table).table :=
  ⟨memoLcs_new_keys left right table,memoLcs_nodup left right table⟩

/-- A query at any two decomposition states only adds keys in the original
product domain. -/
theorem MemoGrowth.decomposition {left right first second : DyckWord} {before after : MemoTable}
    (h : MemoGrowth (MemoDomain first second) before after)
    (hs : MemoDomain left right (first,second)) : MemoGrowth (MemoDomain left right) before after :=
  h.mono (fun _ hd => hd.trans hs)

/-- All child/first-pair-deletion queries made by guided reconstruction
belong to the enclosing pattern/input decomposition product. -/
theorem memoDomain_components (ph pt ih it : DyckWord) :
    MemoDomain (ph.nest+pt) (ih.nest+it) (ph,ih) ∧
    MemoDomain (ph.nest+pt) (ih.nest+it) (pt,it) ∧
    MemoDomain (ph.nest+pt) (ih.nest+it) (ph.nest+pt,ih+it) := by
  have hp := BalancedDecomposition.states_closed (BalancedDecomposition.mem_states_self (ph.nest+pt))
    (BalancedDecomposition.nest_add_ne_zero ph pt)
  have hi := BalancedDecomposition.states_closed (BalancedDecomposition.mem_states_self (ih.nest+it))
    (BalancedDecomposition.nest_add_ne_zero ih it)
  simp only [DyckWord.insidePart_add DyckWord.nest_ne_zero,DyckWord.insidePart_nest,
    DyckWord.outsidePart_add DyckWord.nest_ne_zero,DyckWord.outsidePart_nest,zero_add] at hp hi
  exact ⟨⟨hp.1,hi.1⟩,⟨hp.2.1,hi.2.1⟩,⟨BalancedDecomposition.mem_states_self _,hi.2.2⟩⟩

/-- Actual unique memo entries confined to any finite combined query domain
have at most its cardinality. This includes multiple original input products. -/
theorem memo_length_le_domain (table : MemoTable) (domain : Finset MemoKey)
    (hn : (table.map Prod.fst).Nodup) (hd : ∀ entry ∈ table, entry.1 ∈ domain) : table.length ≤ domain.card := by
  have hsub : (table.map Prod.fst).toFinset ⊆ domain := by
    intro key hk
    obtain ⟨entry,he,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hk)
    exact hd entry he
  have hh := Finset.card_le_card hsub
  simpa only [List.toFinset_card_of_nodup hn,List.length_map] using hh

/-- Three actual query families suffice for an original shape optimization
followed by pattern-to-left and pattern-to-right reconstruction feasibility. -/
def guidedDomain (left right pattern : DyckWord) : Finset MemoKey :=
  (BalancedDecomposition.states left).product (BalancedDecomposition.states right) ∪
    (BalancedDecomposition.states pattern).product (BalancedDecomposition.states left) ∪
    (BalancedDecomposition.states pattern).product (BalancedDecomposition.states right)

/-- The combined domain is finite without assuming that the output pattern is
itself a decomposition state of either original input. -/
theorem guidedDomain_card (left right pattern : DyckWord) :
    (guidedDomain left right pattern).card ≤
      (BalancedDecomposition.states left).card*(BalancedDecomposition.states right).card +
      (BalancedDecomposition.states pattern).card*(BalancedDecomposition.states left).card +
      (BalancedDecomposition.states pattern).card*(BalancedDecomposition.states right).card := by
  unfold guidedDomain
  have houter := Finset.card_union_le
    ((BalancedDecomposition.states left).product (BalancedDecomposition.states right) ∪
      (BalancedDecomposition.states pattern).product (BalancedDecomposition.states left))
    ((BalancedDecomposition.states pattern).product (BalancedDecomposition.states right))
  have hinner := Finset.card_union_le
    ((BalancedDecomposition.states left).product (BalancedDecomposition.states right))
    ((BalancedDecomposition.states pattern).product (BalancedDecomposition.states left))
  simpa only [Finset.product_eq_sprod,Finset.card_product] using houter.trans (Nat.add_le_add_right hinner _)

/-- An actual memo table with distinct keys entirely in a chosen finite
combined query domain. The table retains values and order. -/
structure MemoWithin (domain : Finset MemoKey) (table : MemoTable) : Prop where
  nodup : (table.map Prod.fst).Nodup
  keys : ∀ entry ∈ table, entry.1 ∈ domain

/-- No initial query contributes any cache key. -/
theorem MemoWithin.empty (domain : Finset MemoKey) : MemoWithin domain [] :=
  ⟨by simp,by simp⟩

/-- Sound growth can be composed while retaining earlier query families. -/
theorem MemoGrowth.within {query : MemoKey → Prop} {domain : Finset MemoKey} {before after : MemoTable}
    (h : MemoGrowth query before after) (hb : MemoWithin domain before)
    (hq : ∀ key, query key → key ∈ domain) : MemoWithin domain after := by
  refine ⟨h.nodup hb.nodup,?_⟩
  intro entry he
  rcases h.new_keys entry he with hi | hn
  · exact hb.keys entry hi
  · exact hq entry.1 hn

theorem MemoWithin.length_le {domain : Finset MemoKey} {table : MemoTable} (h : MemoWithin domain table) :
    table.length ≤ domain.card := memo_length_le_domain table domain h.nodup h.keys

theorem MemoDomain.guided_original {left right pattern : DyckWord} {key : MemoKey} (h : MemoDomain left right key) :
    key ∈ guidedDomain left right pattern := by
  simp only [guidedDomain,Finset.product_eq_sprod,Finset.mem_union,Finset.mem_product]
  exact Or.inl (Or.inl h)

theorem MemoDomain.guided_left {left right pattern : DyckWord} {key : MemoKey} (h : MemoDomain pattern left key) :
    key ∈ guidedDomain left right pattern := by
  simp only [guidedDomain,Finset.product_eq_sprod,Finset.mem_union,Finset.mem_product]
  exact Or.inl (Or.inr h)

theorem MemoDomain.guided_right {left right pattern : DyckWord} {key : MemoKey} (h : MemoDomain pattern right key) :
    key ∈ guidedDomain left right pattern := by
  simp only [guidedDomain,Finset.product_eq_sprod,Finset.mem_union,Finset.mem_product]
  exact Or.inr h

/-- Every key in the complete guided family has a total original-input length
budget and a minimum-side budget. A genuine common pattern is bounded by both
original inputs, even when its decomposition states are new query shapes. -/
theorem guidedDomain_lengths {left right pattern : DyckWord}
    (hpl : pattern.semilength ≤ left.semilength) (hpr : pattern.semilength ≤ right.semilength)
    (key : MemoKey) (hk : key ∈ guidedDomain left right pattern) :
    key.1.semilength+key.2.semilength ≤ left.semilength+right.semilength ∧
      min key.1.semilength key.2.semilength ≤ min left.semilength right.semilength := by
  simp only [guidedDomain,Finset.product_eq_sprod,Finset.mem_union,Finset.mem_product] at hk
  rcases hk with (hk | hk) | hk
  · have hl := BalancedDecomposition.states_semilength_le hk.1
    have hr := BalancedDecomposition.states_semilength_le hk.2
    constructor <;> omega
  · have hl := BalancedDecomposition.states_semilength_le hk.1
    have hr := BalancedDecomposition.states_semilength_le hk.2
    constructor <;> omega
  · have hl := BalancedDecomposition.states_semilength_le hk.1
    have hr := BalancedDecomposition.states_semilength_le hk.2
    constructor <;> omega

end SubtreeProofs.Paper2004.OrderedTree

end
