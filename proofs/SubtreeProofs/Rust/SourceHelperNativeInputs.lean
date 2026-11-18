module

public import SubtreeProofs.Rust.SourceOwnerCallees

/-! Independent snapshot types recover finite native helper inputs. These are
input-shape facts, without fuel, execution, expected-output or cache-soundness
premises. Numeric reconstruction preserves the original u32 width requirement. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

open verified_ordered_core Aeneas Aeneas.Std

theorem SnapshotTyped.shared_value {value : Value} {ty : Ty} (h : SnapshotTyped value (.shared ty)) :
    ∃ inner, value = .reference inner ∧ SnapshotTyped inner ty := by
  cases h with
  | shared inner => exact ⟨_, rfl, inner⟩
  | node shape _ => cases shape

theorem SnapshotTyped.owned_value {value : Value} {ty : Ty} (h : SnapshotTyped value (.owned ty)) :
    ∃ inner, value = .boxed inner ∧ SnapshotTyped inner ty := by
  cases h with
  | owned inner => exact ⟨_, rfl, inner⟩
  | node shape _ => cases shape

theorem SnapshotTyped.native_word {value : Value} (h : SnapshotTyped value (.adt .word)) :
    ∃ word : BalancedWord, value = encodeWord word := by
  cases h with
  | node shape fields =>
    cases shape with
    | emptyWord => cases fields; exact ⟨.Empty, rfl⟩
    | pairWord =>
      cases fields with
      | cons head rest => cases rest with
        | cons tail last =>
          cases last
          obtain ⟨_, rfl, hhead⟩ := head.owned_value
          obtain ⟨_, rfl, htail⟩ := tail.owned_value
          obtain ⟨left, rfl⟩ := hhead.native_word
          obtain ⟨right, rfl⟩ := htail.native_word
          exact ⟨.Pair left right, rfl⟩
termination_by sizeOf value

theorem SnapshotTyped.native_result {value : Value} (h : SnapshotTyped value (.adt .embedding)) :
    ∃ result : CommonEmbedding, value = encodeResult result := by
  cases h with
  | node shape fields =>
    cases shape with
    | embedding => cases fields with
      | cons word rest => cases rest with
        | cons score last =>
          cases last
          obtain ⟨native, rfl⟩ := word.native_word
          obtain ⟨number, rfl, bound⟩ := SourceEval.Types.typed_u32 score
          refine ⟨⟨native, U32.ofNatCore number bound⟩, ?_⟩
          simp only [encodeResult, U32.ofNatCore_val_eq]

theorem SnapshotTyped.native_entry {value : Value} (h : SnapshotTyped value (.adt .entry)) :
    ∃ entry : MemoEntry, value = .node .entry 0 [encodeWord entry.left, encodeWord entry.right, encodeResult entry.result] := by
  cases h with
  | node shape fields =>
    cases shape with
    | entry => cases fields with
      | cons leftTyped rest => cases rest with
        | cons rightTyped rest => cases rest with
          | cons resultTyped last =>
            cases last
            obtain ⟨left, rfl⟩ := leftTyped.native_word
            obtain ⟨right, rfl⟩ := rightTyped.native_word
            obtain ⟨result, rfl⟩ := resultTyped.native_result
            exact ⟨⟨left, right, result⟩, rfl⟩

theorem SnapshotTyped.native_table {value : Value} (h : SnapshotTyped value (.adt .table)) :
    ∃ table : MemoTable, value = encodeTable table := by
  cases h with
  | node shape fields =>
    cases shape with
    | emptyTable => cases fields; exact ⟨.Empty, rfl⟩
    | entryTable => cases fields with
      | cons entryField rest => cases rest with
        | cons tableField last =>
          cases last
          obtain ⟨_, rfl, entryTyped⟩ := entryField.owned_value
          obtain ⟨_, rfl, tableTyped⟩ := tableField.owned_value
          obtain ⟨entry, rfl⟩ := entryTyped.native_entry
          obtain ⟨table, rfl⟩ := tableTyped.native_table
          exact ⟨.Entry entry table, rfl⟩
termination_by sizeOf value

end SubtreeProofs.Rust.LookupSource.Heap
