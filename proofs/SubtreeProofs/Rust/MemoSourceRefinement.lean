module

public import SubtreeProofs.Rust.MemoSourceCertificate
public import SubtreeProofs.Rust.LookupSourceRefinement

/-! Successful execution of actual memo primitive bodies. Functional outputs
are compared with the independent owned-word/table models; all local and callee
costs remain in the source execution. Heap refinement is separate. -/

@[expose] public section

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

namespace SubtreeProofs.Rust.MemoSource

open LookupSource verified_ordered_core

attribute [local lookup_source_simps] Program.body Program.copyWord Program.copyResult
  Program.concatenate Program.insert entryEvents

theorem box_run (fuel : Nat) (hf : 0 < fuel) (value : Value) :
    run Program.body fuel .boxNew [value] =
      some (.boxed value, ⟨1, { allocations := 1 }⟩) := by
  cases fuel with
  | zero => omega
  | succ fuel => rw [run_succ]; rfl

theorem copy_empty (fuel : Nat) :
    run Program.body (fuel + 1) .copyWord [.reference (encodeWord .Empty)] =
      some (encodeWord .Empty, ⟨10, { copyNodes := 1 }⟩) := by
  rw [run_succ]
  simp only [lookup_source_simps, encodeWord]
  rfl

theorem copy_source (word : BalancedWord) (fuel : Nat) (hf : wordHeight word ≤ fuel) :
    ∃ cost, run Program.body fuel .copyWord [.reference (encodeWord word)] =
      some (encodeWord word, cost) ∧ cost.events = (LookupEvents.copy word).2 := by
  induction word generalizing fuel with
  | Empty =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel => exact ⟨_, copy_empty fuel, rfl⟩
  | Pair head tail ihHead ihTail =>
    cases fuel with
    | zero => simp [wordHeight] at hf
    | succ fuel =>
      have hh : wordHeight head ≤ fuel := by simp only [wordHeight] at hf; omega
      have ht : wordHeight tail ≤ fuel := by simp only [wordHeight] at hf; omega
      have hp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos head) hh
      obtain ⟨ch, heh, hch⟩ := ihHead fuel hh
      obtain ⟨ct, het, hct⟩ := ihTail fuel ht
      have hbox := fun value => box_run fuel hp value
      rw [run_succ]
      simp [lookup_source_simps, encodeWord, heh, het, hbox, LookupEvents.copy,
        LookupEvents.Events.plus, hch, hct]
      omega

theorem copyResult_source (result : CommonEmbedding) (fuel : Nat)
    (hf : wordHeight result.word + 1 ≤ fuel) :
    ∃ cost, run Program.body fuel .copyResult [.reference (encodeResult result)] =
      some (encodeResult result, cost) ∧ cost.events = (LookupEvents.copyResult result).2 := by
  cases fuel with
  | zero => omega
  | succ fuel =>
    have hh : wordHeight result.word ≤ fuel := by omega
    obtain ⟨cw, hew, hcw⟩ := copy_source result.word fuel hh
    rw [run_succ]
    simp [lookup_source_simps, encodeResult, hew, LookupEvents.copyResult,
      LookupEvents.Events.plus, hcw]
    omega

/-- Concatenation's full structural copy work, with all Boxes explicit. -/
def concatenateEvents : BalancedWord → BalancedWord → LookupEvents.Events
  | .Empty, right => (LookupEvents.copy right).2
  | .Pair head tail, right =>
    ((LookupEvents.copy head).2.plus (concatenateEvents tail right)).plus { allocations := 2 }

def concatenateDepth : BalancedWord → BalancedWord → Nat
  | .Empty, right => wordHeight right + 1
  | .Pair head tail, right => 1 + max (wordHeight head) (concatenateDepth tail right)

theorem concatenate_source (left right : BalancedWord) (fuel : Nat)
    (hf : concatenateDepth left right ≤ fuel) :
    ∃ cost, run Program.body fuel .concatenate
        [.reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      cost.events = concatenateEvents left right := by
  induction left generalizing fuel with
  | Empty =>
    cases fuel with
    | zero => simp [concatenateDepth] at hf
    | succ fuel =>
      obtain ⟨cw, hw, hc⟩ := copy_source right fuel (by simpa [concatenateDepth] using hf)
      rw [run_succ]
      simp [lookup_source_simps, encodeWord, hw, concatenateEvents, OrderedSolver.appendWord, hc]
  | Pair head tail ihHead ihTail =>
    cases fuel with
    | zero => simp [concatenateDepth] at hf
    | succ fuel =>
      have hh : wordHeight head ≤ fuel := by simp only [concatenateDepth] at hf; omega
      have ht : concatenateDepth tail right ≤ fuel := by simp only [concatenateDepth] at hf; omega
      have hp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos head) hh
      obtain ⟨ch, heh, hch⟩ := copy_source head fuel hh
      obtain ⟨ct, het, hct⟩ := ihTail fuel ht
      have hbox := fun value => box_run fuel hp value
      rw [run_succ]
      simp [lookup_source_simps, encodeWord, heh, het, hbox, concatenateEvents,
        OrderedSolver.appendWord, LookupEvents.Events.plus, hch, hct]
      omega

def insertDepth (left right : BalancedWord) (result : CommonEmbedding) : Nat :=
  1 + max (wordHeight left) (max (wordHeight right) (wordHeight result.word + 1))

def insertEvents (left right : BalancedWord) (result : CommonEmbedding) : LookupEvents.Events :=
  (((LookupEvents.copy left).2.plus (LookupEvents.copy right).2).plus
    (LookupEvents.copyResult result).2).plus { allocations := 2 }

/-- The owned input table is moved once into the new tail; copies are made
only of the two keys and supplied witness, with no cache-soundness premise. -/
theorem insert_source (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) :
    ∃ cost, run Program.body fuel .insert
        [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
      some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧ cost.events = insertEvents left right result := by
  cases fuel with
  | zero => simp [insertDepth] at hf
  | succ fuel =>
    have hl : wordHeight left ≤ fuel := by simp only [insertDepth] at hf; omega
    have hr : wordHeight right ≤ fuel := by simp only [insertDepth] at hf; omega
    have hc : wordHeight result.word + 1 ≤ fuel := by simp only [insertDepth] at hf; omega
    have hp : 0 < fuel := lt_of_lt_of_le (wordHeight_pos left) hl
    obtain ⟨cl, hel, hcl⟩ := copy_source left fuel hl
    obtain ⟨cr, her, hcr⟩ := copy_source right fuel hr
    obtain ⟨cc, hec, hcc⟩ := copyResult_source result fuel hc
    simp only [encodeResult] at hec
    have hbox := fun value => box_run fuel hp value
    rw [run_succ]
    simp [lookup_source_simps, encodeTable, encodeResult, hel, her, hec, hbox, insertEvents,
      LookupEvents.Events.plus, hcl, hcr, hcc]
    omega

theorem insertEvents_exact (left right : BalancedWord) (result : CommonEmbedding) :
    insertEvents left right result =
      ⟨0, 0, 2 * ((OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength +
        (OrderedSolver.toDyck result.word).semilength) + 3,
        2 * ((OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength +
        (OrderedSolver.toDyck result.word).semilength) + 2, 1⟩ := by
  simp only [insertEvents, LookupEvents.copy_exact, LookupEvents.copyResult_exact, LookupEvents.Events.plus]
  congr 1 <;> omega

theorem concatenateEvents_bound (left right : BalancedWord) :
    (concatenateEvents left right).allocations =
        2 * ((OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength) ∧
    (concatenateEvents left right).copyNodes ≤
        2 * ((OrderedSolver.toDyck left).semilength + (OrderedSolver.toDyck right).semilength) + 1 ∧
    (concatenateEvents left right).lookupNodes = 0 ∧
    (concatenateEvents left right).compareNodes = 0 ∧
    (concatenateEvents left right).resultCopies = 0 := by
  induction left with
  | Empty => simp [concatenateEvents, LookupEvents.copy_exact, OrderedSolver.toDyck]
  | Pair head tail ihHead ihTail =>
    simp only [concatenateEvents, LookupEvents.copy_exact, LookupEvents.Events.plus,
      OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
    obtain ⟨ha, hc, hl, he, hr⟩ := ihTail
    exact ⟨by omega, by omega, by simpa using hl, by simpa using he, by simpa using hr⟩

/-- Concrete source and translated native concatenation agree on the independent
append model; the full source execution and work component are retained. -/
theorem concatenate_checked (left right : BalancedWord) (fuel : Nat)
    (hf : concatenateDepth left right ≤ fuel) :
    ∃ cost, sourceRun Certificate.original.body fuel .concatenate
        [.reference (encodeWord left), .reference (encodeWord right)] =
      some (encodeWord (OrderedSolver.appendWord left right), cost) ∧
      verified_ordered_core.concatenate left right = .ok (OrderedSolver.appendWord left right) ∧
      cost.events = concatenateEvents left right := by
  obtain ⟨cost, hrun, he⟩ := concatenate_source left right fuel hf
  exact ⟨cost, by simpa only [Certificate.original_run] using hrun,
    OrderedSolver.concatenate_correct left right, he⟩

theorem insert_checked (table : MemoTable) (left right : BalancedWord) (result : CommonEmbedding) (fuel : Nat)
    (hf : insertDepth left right result ≤ fuel) :
    ∃ cost, sourceRun Certificate.original.body fuel .insert
        [encodeTable table, .reference (encodeWord left), .reference (encodeWord right), .reference (encodeResult result)] =
      some (encodeTable (.Entry ⟨left, right, result⟩ table), cost) ∧
      verified_ordered_core.memo_insert table left right result = .ok (.Entry ⟨left, right, result⟩ table) ∧
      cost.events = insertEvents left right result := by
  obtain ⟨cost, hrun, he⟩ := insert_source table left right result fuel hf
  exact ⟨cost, by simpa only [Certificate.original_run] using hrun,
    MemoizedOrderedSolver.memo_insert_correct table left right result, he⟩

end SubtreeProofs.Rust.MemoSource
