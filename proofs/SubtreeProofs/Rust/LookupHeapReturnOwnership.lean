module

public import SubtreeProofs.Rust.LookupHeapLayout

/-! Exclusive returned ownership for the actual generated lookup fragment.
Every newly allocated Box is reachable exactly once from the returned result;
no old input cell becomes owned by that result. These are final-state claims.
Safe resets/destruction at intermediate states and stack lifetimes still need
their own simulation; they are not consequences of final reachability alone. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

open verified_ordered_core

theorem copy_return_owns (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel)
    (memory : Memory) (pointer : Pointer)
    (hrep : Represents memory (.shared pointer) (.reference (encodeWord word)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .copyWord [.shared pointer] memory = some (cell, after, cost)) :
    Owns after cell memory.length after.length := by
  obtain ⟨reference, hs⟩ := Layout.copy_layout word fuel hf memory pointer hrep
  rw [hr] at hs
  cases hs
  exact packWord_owns word memory

theorem copyResult_return_owns (value : CommonEmbedding) (fuel : Nat)
    (hf : wordHeight value.word + 1 ≤ fuel) (memory : Memory) (pointer : Pointer)
    (hrep : Represents memory (.shared pointer) (.reference (encodeResult value)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .copyResult [.shared pointer] memory = some (cell, after, cost)) :
    Owns after cell memory.length after.length := by
  obtain ⟨reference, hs⟩ := Layout.copyResult_layout value fuel hf memory pointer hrep
  rw [hr] at hs
  cases hs
  exact packResult_owns value memory

theorem lookup_return_owns (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    Owns after cell memory.length after.length := by
  obtain ⟨reference, hs⟩ := Layout.lookup_layout table left right fuel hf memory pt pl pr hTable hLeft hRight
  rw [hr] at hs
  cases hs
  exact Layout.outputLayout_owns _ memory

/-- A complete ownership-occurrence ledger, not a set that could erase
duplicate aliases. Its size is exactly the actual Box-allocation counter. -/
theorem lookup_return_footprint (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    {cell : Cell} {after : Memory} {cost : Cost}
    (hr : run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost)) :
    ∃ addresses, Footprint after cell addresses ∧ addresses.Nodup ∧
      addresses.length = cost.events.allocations ∧
      (∀ address, address ∈ addresses ↔ memory.length ≤ address ∧ address < after.length) ∧
      Extends memory after := by
  have ho := lookup_return_owns table left right fuel hf memory pt pl pr hTable hLeft hRight hr
  obtain ⟨_, _, hext, hlen, _, _⟩ := lookup_all_runs table left right memory _
    (.cons hTable (.cons hLeft (.cons hRight .nil))) fuel hf hr
  have hex := ho.exclusive ho.footprint
  refine ⟨List.range' memory.length (after.length - memory.length), ho.footprint,
    hex.2.1, ?_, hex.2.2, hext⟩
  simp only [List.length_range']
  omega

/-- No input-owned cell can be silently reused as an output Box. Shared
input aliasing is still allowed by the independent representation premises. -/
theorem lookup_no_old_owned_alias (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    {cell : Cell} {after : Memory} {cost : Cost} {addresses : List Nat}
    (hr : run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory = some (cell, after, cost))
    (hp : Footprint after cell addresses) {address : Nat} (hi : address < memory.length) :
    address ∉ addresses := by
  have ho := lookup_return_owns table left right fuel hf memory pt pl pr hTable hLeft hRight hr
  have hex := ho.exclusive hp
  intro ha
  have hlo := (hex.2.2 address).mp ha
  omega

end SubtreeProofs.Rust.LookupSource.Heap
