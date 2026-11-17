module

public import SubtreeProofs.Rust.LookupHeapRefinement
public import SubtreeProofs.Rust.LookupHeapOwnership

/-! Exact output layouts of the actual generated copying/lookup bodies.
The existing representation theorem alone would permit duplicated Box aliases;
these theorems connect execution to fresh postorder ownership intervals. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap.Layout

open verified_ordered_core

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

attribute [local heap_layout_simps] Heap.exec action scrutinee rvalue operand operands
  locate borrow initialLocals Locals.set selectBranch Action.weight RValue.weight
  Operand.weight Place.weight Scrutinee.weight Cost.plus entryEvents LookupEvents.Events.plus
  Program.body Program.copyWord Program.copyResult Program.lookup bind Option.bind

@[local simp] theorem root_field (address index : Nat) :
    (Pointer.field ⟨address, []⟩ index) = ⟨address, [index]⟩ := rfl

theorem run_step (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Cell) (memory : Memory) :
    Heap.run body (fuel + 1) function args memory =
      (if function = .boxNew then
        match args with
        | [value] => some ((alloc memory value).1, (alloc memory value).2, ⟨1, entryEvents function⟩)
        | _ => none
      else do
        let (outcome, memory, cost) ← Heap.exec (Heap.run body fuel) (body function) memory (initialLocals args)
        match outcome with
        | .next _ => none
        | .returned value => some (value, memory, (⟨1, entryEvents function⟩ : Cost).plus cost)) := by rfl

theorem box_layout (fuel : Nat) (hf : 0 < fuel) (memory : Memory) (value : Cell) :
    Heap.run Program.body fuel .boxNew [value] memory =
      some ((alloc memory value).1, (alloc memory value).2, ⟨1, entryEvents .boxNew⟩) := by
  cases fuel with
  | zero => omega
  | succ fuel => rw [run_step]; rfl

theorem copy_layout (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel)
    (memory : Memory) (pointer : Pointer)
    (hrep : Represents memory (.shared pointer) (.reference (encodeWord word))) :
    ∃ cost, Heap.run Program.body fuel .copyWord [.shared pointer] memory =
      some ((packWord word memory).1, (packWord word memory).2, cost) := by
  induction word generalizing fuel memory pointer with
  | Empty =>
    cases hrep with
    | shared hr hp =>
      cases hp with
      | node hs =>
        cases hs
        cases fuel with
        | zero => simp [wordHeight] at hf
        | succ fuel =>
          rw [run_step]
          simp [heap_layout_simps, hr, packWord]
  | Pair head tail ihHead ihTail =>
    cases hrep with
    | shared hr hp =>
      cases hp with
      | node hs =>
        cases hs with
        | cons hh hs =>
          cases hs with
          | cons ht hs =>
            cases hs
            cases hh with
            | @owned ah ch _ hhr hhead =>
              cases ht with
              | @owned atTail ct _ htr htail =>
                cases fuel with
                | zero => simp [wordHeight] at hf
                | succ fuel =>
                  have hfh : wordHeight head ≤ fuel := by simp only [wordHeight] at hf; omega
                  have hft : wordHeight tail ≤ fuel := by simp only [wordHeight] at hf; omega
                  have hfp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos head) hfh
                  have hheadRef : Represents memory (.shared ⟨ah, []⟩) (.reference (encodeWord head)) :=
                    .shared (by simpa [read, fields] using hhr) hhead
                  obtain ⟨hc, hh⟩ := ihHead fuel hfh memory ⟨ah, []⟩ hheadRef
                  have he : Extends memory (alloc (packWord head memory).2 (packWord head memory).1).2 :=
                    (packWord_spec head memory).2.trans
                      (Extends.append (packWord head memory).2 [(packWord head memory).1])
                  have htailRef : Represents (alloc (packWord head memory).2 (packWord head memory).1).2
                      (.shared ⟨atTail, []⟩) (.reference (encodeWord tail)) :=
                    (Represents.shared (by simpa [read, fields] using htr) htail).mono he
                  obtain ⟨tc, ht⟩ := ihTail fuel hft
                    (alloc (packWord head memory).2 (packWord head memory).1).2 ⟨atTail, []⟩ htailRef
                  have hfieldh : read memory (pointer.field 0) = some (.owned ah) := by
                    rw [read_field hr]; rfl
                  have hfieldt : read (alloc (packWord head memory).2 (packWord head memory).1).2
                      (pointer.field 1) = some (.owned atTail) := by
                    rw [read_field (read_extends he hr)]; rfl
                  have htailRead := he atTail ct htr
                  have hb := box_layout fuel hfp
                  rw [run_step]
                  simp [heap_layout_simps, hr, hfieldh, hhr, hh, hb,
                    hfieldt, htailRead, ht, packWord]

theorem copyResult_layout (value : CommonEmbedding) (fuel : Nat)
    (hf : wordHeight value.word + 1 ≤ fuel) (memory : Memory) (pointer : Pointer)
    (hrep : Represents memory (.shared pointer) (.reference (encodeResult value))) :
    ∃ cost, Heap.run Program.body fuel .copyResult [.shared pointer] memory =
      some ((packResult value memory).1, (packResult value memory).2, cost) := by
  cases hrep with
  | shared hr hp =>
    cases hp with
    | node hs =>
      cases hs with
      | cons hw hs =>
        cases hs with
        | cons hn hs =>
          cases hs
          cases hn
          cases fuel with
          | zero => omega
          | succ fuel =>
            have hf' : wordHeight value.word ≤ fuel := by omega
            have hwfield := read_field (index := 0) hr
            simp only [List.getElem?_cons_zero] at hwfield
            have hwref := Represents.shared hwfield hw
            obtain ⟨cost, hcopy⟩ := copy_layout value.word fuel hf' memory (pointer.field 0) hwref
            have hafter := read_extends (packWord_spec value.word memory).2 hr
            rw [run_step]
            simp [heap_layout_simps, hr, hwfield, hcopy, hafter, packResult]

theorem shared_view {memory : Memory} {pointer : Pointer} {value : Value}
    (h : Represents memory (.shared pointer) (.reference value)) :
    ∃ cell, read memory pointer = some cell ∧ Represents memory cell value := by
  cases h with | shared hr hv => exact ⟨_, hr, hv⟩

theorem entry_view (entry : MemoEntry) (rest : MemoTable) (memory : Memory) (pointer : Pointer)
    (h : Represents memory (.shared pointer) (.reference (encodeTable (.Entry entry rest)))) :
    ∃ ae ar lc rc ec cr,
      read memory pointer = some (.node .table 1 [.owned ae, .owned ar]) ∧
      memory[ae]? = some (.node .entry 0 [lc, rc, ec]) ∧ memory[ar]? = some cr ∧
      Represents memory lc (encodeWord entry.left) ∧ Represents memory rc (encodeWord entry.right) ∧
      Represents memory ec (encodeResult entry.result) ∧ Represents memory cr (encodeTable rest) := by
  cases h with
  | shared hr hp => cases hp with
    | node hs => cases hs with
      | cons he hs => cases hs with
        | cons ht hs =>
          cases hs
          cases he with
          | @owned ae ce _ her he => cases ht with
            | @owned ar cr _ htr ht => cases he with
              | node he => cases he with
                | cons hl he => cases he with
                  | cons hright he => cases he with
                    | cons hresult he =>
                      cases he
                      exact ⟨ae, ar, _, _, _, cr, hr, her, htr, hl, hright, hresult, ht⟩

def outputLayout : Option CommonEmbedding → Memory → Cell × Memory
  | none, memory => (.node .optional 0 [], memory)
  | some value, memory =>
    let (cell, after) := packResult value memory
    (.node .optional 1 [cell], after)

theorem outputLayout_owns (value : Option CommonEmbedding) (memory : Memory) :
    Owns (outputLayout value memory).2 (outputLayout value memory).1 memory.length
      (outputLayout value memory).2.length := by
  cases value with
  | none => exact .node (.nil _)
  | some value => exact .node (.cons (packResult_owns value memory) (.nil _))

theorem lookup_layout (table : MemoTable) (left right : BalancedWord) (fuel : Nat)
    (hf : lookupDepth table left right ≤ fuel) (memory : Memory) (pt pl pr : Pointer)
    (hTable : Represents memory (.shared pt) (.reference (encodeTable table)))
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cost, Heap.run Program.body fuel .lookup [.shared pt, .shared pl, .shared pr] memory =
      some ((outputLayout (LookupEvents.lookup table left right).1 memory).1,
        (outputLayout (LookupEvents.lookup table left right).1 memory).2, cost) := by
  induction table generalizing fuel memory pt pl pr with
  | Empty =>
    cases hTable with
    | shared hr hp => cases hp with
      | node hs =>
        cases hs
        cases fuel with
        | zero => simp [lookupDepth, tableHeight] at hf
        | succ fuel =>
          rw [run_step]
          simp [heap_layout_simps, hr, LookupEvents.lookup, outputLayout]
  | Entry entry rest ih =>
    obtain ⟨ae, ar, lc, rc, ec, cr, hroot, he, ht, hl, hr, hc, hs⟩ := entry_view entry rest memory pt hTable
    obtain ⟨lcell, hlread, hlrep⟩ := shared_view hLeft
    obtain ⟨rcell, hrread, hrrep⟩ := shared_view hRight
    have hEntry : read memory ⟨ae, []⟩ = some (.node .entry 0 [lc, rc, ec]) := by
      simpa [read, fields] using he
    have hEntryPtr : read memory (pt.field 0) = some (.owned ae) := by rw [read_field hroot]; rfl
    have hRestPtr : read memory (pt.field 1) = some (.owned ar) := by rw [read_field hroot]; rfl
    have hL : read memory ⟨ae, [0]⟩ = some lc := by simpa [Pointer.field] using read_field (index := 0) hEntry
    have hR : read memory ⟨ae, [1]⟩ = some rc := by simpa [Pointer.field] using read_field (index := 1) hEntry
    have hC : read memory ⟨ae, [2]⟩ = some ec := by simpa [Pointer.field] using read_field (index := 2) hEntry
    have hRest : Represents memory (.shared ⟨ar, []⟩) (.reference (encodeTable rest)) :=
      .shared (by simpa [read, fields] using ht) hs
    cases fuel with
    | zero => simp [lookupDepth, tableHeight] at hf
    | succ fuel =>
      have hfl : wordHeight left ≤ fuel := by simp only [lookupDepth, tableHeight] at hf; omega
      have hfr : wordHeight right ≤ fuel := by simp only [lookupDepth, tableHeight] at hf; omega
      have hfc : wordHeight entry.result.word + 1 ≤ fuel := by simp only [lookupDepth, tableHeight] at hf; omega
      have hfs : lookupDepth rest left right ≤ fuel := by simp only [lookupDepth, tableHeight] at hf ⊢; omega
      obtain ⟨cl, hcl, _⟩ := Heap.compare_spec left entry.left memory
        [.shared pl, .shared ⟨ae, [0]⟩] (.cons hLeft (.cons (.shared hL hl) .nil)) fuel hfl
      obtain ⟨cc, hcr, _⟩ := Heap.compare_spec right entry.right memory
        [.shared pr, .shared ⟨ae, [1]⟩] (.cons hRight (.cons (.shared hR hr) .nil)) fuel hfr
      obtain ⟨cw, hcw⟩ := copyResult_layout entry.result fuel hfc memory ⟨ae, [2]⟩ (.shared hC hc)
      obtain ⟨cs, hcs⟩ := ih fuel hfs memory ⟨ar, []⟩ pl pr hRest hLeft hRight
      cases hbl : (LookupEvents.compare left entry.left).1
      all_goals cases hbr : (LookupEvents.compare right entry.right).1
      all_goals rw [run_step]
      all_goals simp [heap_layout_simps, hroot, hEntryPtr, hRestPtr, he, ht,
        hlread, hrread, hL, hR, hC, hcl, hcr, hcw, hcs, hbl, hbr,
        outputLayout, LookupEvents.lookup, LookupEvents.copyResult_exact]

end SubtreeProofs.Rust.LookupSource.Heap.Layout
