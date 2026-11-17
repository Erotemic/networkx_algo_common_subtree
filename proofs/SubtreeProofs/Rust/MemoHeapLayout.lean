module

public import SubtreeProofs.Rust.MemoHeapExecution
public import SubtreeProofs.Rust.LookupHeapOwnership

/-! Exact postorder output layouts of the actual memo helper bodies. Copy and
concatenation results own fresh intervals; insertion additionally transfers the
existing table, which must not be silently copied or declared fresh. -/

@[expose] public section

namespace SubtreeProofs.Rust.MemoSource.Heap.Layout

open LookupSource LookupSource.Heap verified_ordered_core

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

attribute [local heap_layout_simps] LookupSource.Heap.exec action scrutinee rvalue operand operands
  locate borrow initialLocals Locals.set selectBranch Action.weight RValue.weight
  Operand.weight Place.weight Scrutinee.weight Cost.plus MemoSource.entryEvents LookupEvents.Events.plus
  Program.body Program.copyWord Program.copyResult Program.concatenate Program.insert bind Option.bind

@[local simp] theorem root_field (address index : Nat) :
    (Pointer.field ⟨address, []⟩ index) = ⟨address, [index]⟩ := rfl

theorem run_step (body : Function → Code) (fuel : Nat) (function : Function)
    (args : List Cell) (memory : Memory) :
    MemoSource.Heap.run body (fuel + 1) function args memory =
      (if function = .boxNew then
        match args with
        | [value] => some ((alloc memory value).1, (alloc memory value).2, ⟨1, entryEvents function⟩)
        | _ => none
      else do
        let (outcome, memory, cost) ← Heap.exec (MemoSource.Heap.run body fuel) (body function) memory (initialLocals args)
        match outcome with
        | .next _ => none
        | .returned value => some (value, memory, (⟨1, entryEvents function⟩ : Cost).plus cost)) := by rfl

theorem box_layout (fuel : Nat) (hf : 0 < fuel) (memory : Memory) (value : Cell) :
    MemoSource.Heap.run Program.body fuel .boxNew [value] memory =
      some ((alloc memory value).1, (alloc memory value).2, ⟨1, entryEvents .boxNew⟩) := by
  cases fuel with
  | zero => omega
  | succ fuel => rw [run_step]; rfl

theorem copy_layout (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel)
    (memory : Memory) (pointer : Pointer)
    (hrep : Represents memory (.shared pointer) (.reference (encodeWord word))) :
    ∃ cost, MemoSource.Heap.run Program.body fuel .copyWord [.shared pointer] memory =
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
                    .shared (by simpa [LookupSource.Heap.read, LookupSource.Heap.fields] using hhr) hhead
                  obtain ⟨hc, hh⟩ := ihHead fuel hfh memory ⟨ah, []⟩ hheadRef
                  have he : Extends memory (alloc (packWord head memory).2 (packWord head memory).1).2 :=
                    (packWord_spec head memory).2.trans
                      (Extends.append (packWord head memory).2 [(packWord head memory).1])
                  have htailRef : Represents (alloc (packWord head memory).2 (packWord head memory).1).2
                      (.shared ⟨atTail, []⟩) (.reference (encodeWord tail)) :=
                    (Represents.shared (by simpa [LookupSource.Heap.read, LookupSource.Heap.fields] using htr) htail).mono he
                  obtain ⟨tc, ht⟩ := ihTail fuel hft
                    (alloc (packWord head memory).2 (packWord head memory).1).2 ⟨atTail, []⟩ htailRef
                  have hfieldh : LookupSource.Heap.read memory (pointer.field 0) = some (.owned ah) := by
                    rw [read_field hr]; rfl
                  have hfieldt : LookupSource.Heap.read (alloc (packWord head memory).2 (packWord head memory).1).2
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
    ∃ cost, MemoSource.Heap.run Program.body fuel .copyResult [.shared pointer] memory =
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
    ∃ cell, LookupSource.Heap.read memory pointer = some cell ∧ Represents memory cell value := by
  cases h with | shared hr hv => exact ⟨_, hr, hv⟩

theorem concatenate_layout (left right : BalancedWord) (fuel : Nat)
    (hf : concatenateDepth left right ≤ fuel) (memory : Memory) (pl pr : Pointer)
    (hLeft : Represents memory (.shared pl) (.reference (encodeWord left)))
    (hRight : Represents memory (.shared pr) (.reference (encodeWord right))) :
    ∃ cost, run Program.body fuel .concatenate [.shared pl, .shared pr] memory =
      some ((packWord (OrderedSolver.appendWord left right) memory).1,
        (packWord (OrderedSolver.appendWord left right) memory).2, cost) := by
  induction left generalizing fuel memory pl pr with
  | Empty =>
    cases fuel with
    | zero => simp [concatenateDepth] at hf
    | succ fuel =>
      have hw : wordHeight right ≤ fuel := by simpa [concatenateDepth] using hf
      obtain ⟨cost, hc⟩ := copy_layout right fuel hw memory pr hRight
      obtain ⟨target, hr, hv⟩ := shared_view hRight
      cases hLeft with
      | shared hl hp => cases hp with
        | node hs =>
          cases hs
          rw [run_step]
          simp [heap_layout_simps, hl, hr, hc, OrderedSolver.appendWord]
  | Pair head tail ihHead ihTail =>
    cases hLeft with
    | shared hr hp => cases hp with
      | node hs => cases hs with
        | cons hh hs => cases hs with
          | cons ht hs =>
            cases hs
            cases hh with
            | @owned ah ch _ hhr hhead => cases ht with
              | @owned atTail ct _ htr htail =>
                cases fuel with
                | zero => simp [concatenateDepth] at hf
                | succ fuel =>
                  have hfh : wordHeight head ≤ fuel := by simp only [concatenateDepth] at hf; omega
                  have hft : concatenateDepth tail right ≤ fuel := by simp only [concatenateDepth] at hf; omega
                  have hfp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos head) hfh
                  have hheadRef : Represents memory (.shared ⟨ah, []⟩) (.reference (encodeWord head)) :=
                    .shared (by simpa [LookupSource.Heap.read, LookupSource.Heap.fields] using hhr) hhead
                  obtain ⟨hc, hh⟩ := copy_layout head fuel hfh memory ⟨ah, []⟩ hheadRef
                  have he : Extends memory (alloc (packWord head memory).2 (packWord head memory).1).2 :=
                    (packWord_spec head memory).2.trans
                      (Extends.append (packWord head memory).2 [(packWord head memory).1])
                  have htailRef : Represents (alloc (packWord head memory).2 (packWord head memory).1).2
                      (.shared ⟨atTail, []⟩) (.reference (encodeWord tail)) :=
                    (Represents.shared (by simpa [LookupSource.Heap.read, LookupSource.Heap.fields] using htr) htail).mono he
                  obtain ⟨tc, ht⟩ := ihTail fuel hft _ ⟨atTail, []⟩ pr htailRef (hRight.mono he)
                  have hfieldh : LookupSource.Heap.read memory (pl.field 0) = some (.owned ah) := by rw [read_field hr]; rfl
                  have hfieldt : LookupSource.Heap.read (alloc (packWord head memory).2 (packWord head memory).1).2
                      (pl.field 1) = some (.owned atTail) := by rw [read_field (read_extends he hr)]; rfl
                  have htailRead := he atTail ct htr
                  obtain ⟨target, hrightRead, _⟩ := shared_view (hRight.mono he)
                  have hb := box_layout fuel hfp
                  rw [run_step]
                  simp [heap_layout_simps, hr, hfieldh, hhr, hh, hb,
                    hfieldt, htailRead, hrightRead, ht, packWord, OrderedSolver.appendWord]

end SubtreeProofs.Rust.MemoSource.Heap.Layout
