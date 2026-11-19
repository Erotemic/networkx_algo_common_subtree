module

public import SubtreeProofs.Rust.MemoHeapLayout
public import SubtreeProofs.Rust.LookupSpatialOwnership

/-! Exact insertion layout and retained input-table ownership. The copied entry
occupies a fresh interval; the tail Box contains the original table cell. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Heap.Layout

open LookupSource LookupSource.Heap verified_ordered_core

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

attribute [local heap_layout_simps] LookupSource.Heap.exec action scrutinee rvalue operand operands
  locate borrow initialLocals Locals.set selectBranch Action.weight RValue.weight
  Operand.weight Place.weight Scrutinee.weight Cost.plus MemoSource.entryEvents LookupEvents.Events.plus
  Program.body Program.copyWord Program.copyResult Program.concatenate Program.insert bind Option.bind

def packInsert (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (memory : Memory) : Cell × Memory :=
  let (entry, memory) := packEntry ⟨left, right, result⟩ memory
  let (entry, memory) := alloc memory entry
  let (tail, memory) := alloc memory table
  (.node .table 1 [entry, tail], memory)

theorem packInsert_spec (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding)
    (memory : Memory) (cell : Cell) (ht : Represents memory cell (encodeTable table)) :
    Represents (packInsert cell left right result memory).2 (packInsert cell left right result memory).1
      (encodeTable (.Entry ⟨left, right, result⟩ table)) ∧ Extends memory (packInsert cell left right result memory).2 := by
  have hp := packEntry_spec ⟨left, right, result⟩ memory
  have he := hp.2.trans (Extends.append _ [(packEntry ⟨left, right, result⟩ memory).1])
  have he' := Extends.append (alloc (packEntry ⟨left, right, result⟩ memory).2
    (packEntry ⟨left, right, result⟩ memory).1).2 [cell]
  exact ⟨.node (.cons ((alloc_rep hp.1).mono he') (.cons (alloc_rep (ht.mono he)) .nil)), he.trans he'⟩

theorem insert_layout (table : Cell) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) (memory : Memory) (pl pr pc : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right)))
    (hResult : Represents memory (.shared pc) (.reference (encodeResult result))) :
    ∃ cost, run Program.body fuel .insert [table, .shared pl, .shared pr, .shared pc] memory =
      some ((packInsert table left right result memory).1, (packInsert table left right result memory).2, cost) := by
  cases fuel with
  | zero => simp [insertDepth] at hf
  | succ fuel =>
    have hl : wordHeight left ≤ fuel := by simp only [insertDepth] at hf; omega
    have hr : wordHeight right ≤ fuel := by simp only [insertDepth] at hf; omega
    have hc : wordHeight result.word + 1 ≤ fuel := by simp only [insertDepth] at hf; omega
    have hp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos left) hl
    obtain ⟨cl, hcl⟩ := copy_layout left fuel hl memory pl hLeft
    have heL := (packWord_spec left memory).2
    obtain ⟨cr, hcr⟩ := copy_layout right fuel hr (packWord left memory).2 pr (hRight.mono heL)
    have heR := heL.trans (packWord_spec right (packWord left memory).2).2
    obtain ⟨cc, hcc⟩ := copyResult_layout result fuel hc (packWord right (packWord left memory).2).2 pc (hResult.mono heR)
    obtain ⟨lc, hReadL, _⟩ := shared_view hLeft
    obtain ⟨rc, hReadR, _⟩ := shared_view (hRight.mono heL)
    obtain ⟨ec, hReadC, _⟩ := shared_view (hResult.mono heR)
    have hb := box_layout fuel hp
    rw [run_step]
    simp [heap_layout_simps, hReadL, hcl, hReadR, hcr, hReadC, hcc, hb, packInsert, packEntry]

end SubtreeProofs.Rust.MemoSource.Heap.Layout
