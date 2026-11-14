module

public import SubtreeProofs.Rust.OrderedSolver
public import SubtreeProofs.Paper2004.MemoizedDynamicProgram

/-!
# Actual Rust memoized ordered solver

The association-list implementation has explicit ownership and no foreign
container model. Its cached witnesses are related to the independent optimum,
with the same deterministic tie policy as the certified mathematical DP.
-/

@[expose] public section

open Aeneas Aeneas.Std Result verified_ordered_core

namespace SubtreeProofs.Rust.MemoizedOrderedSolver

open Paper2004.OrderedTree OrderedSolver

abbrev RustMemo := verified_ordered_core.MemoTable

deriving instance DecidableEq for BalancedWord

/-- The representation map is injective by its proved inverse. -/
theorem toDyck_injective : Function.Injective toDyck := by
  intro first second heq
  have h := congrArg fromDyck heq
  simpa only [fromDyck_toDyck] using h

@[simp] theorem toDyck_eq_iff (first second : BalancedWord) : toDyck first = toDyck second ↔ first = second :=
  ⟨fun h => toDyck_injective h, congrArg toDyck⟩

/-- Translated structural equality terminates and decides actual value equality. -/
theorem words_equal_correct (first second : BalancedWord) :
    words_equal first second = .ok (decide (first = second)) := by
  induction first generalizing second with
  | Empty => cases second <;> rw [words_equal] <;> rfl
  | Pair head tail ihHead ihTail =>
    cases second with
    | Empty => rw [words_equal]; rfl
    | Pair sh st =>
      rw [words_equal, ihHead, bind_ok]
      by_cases hh : head = sh
      · subst sh
        simp only [decide_true, ↓reduceIte, ihTail, BalancedWord.Pair.injEq, true_and]
      · simp [hh]

theorem copy_result_correct (result : verified_ordered_core.CommonEmbedding) :
    copy_result result = .ok result := by
  rw [copy_result, copy_word_correct, bind_ok]

/-- A cached result is the independently certified witness for its input key. -/
def Consistent (left right : BalancedWord) (result : verified_ordered_core.CommonEmbedding) : Prop :=
  toDyck result.word = paperCommon (toDyck left) (toDyck right) ∧
    result.edges.val = (toDyck result.word).semilength

/-- Every stored entry has an independently meaningful result. -/
def TableSound : RustMemo → Prop
  | .Empty => True
  | .Entry entry rest => Consistent entry.left entry.right entry.result ∧ TableSound rest

/-- Pure structural lookup used only as a representation model. -/
def findResult : RustMemo → BalancedWord → BalancedWord → Option verified_ordered_core.CommonEmbedding
  | .Empty, _, _ => none
  | .Entry entry rest, left, right =>
    if left = entry.left ∧ right = entry.right then some entry.result else findResult rest left right

/-- The real translated Rust lookup implements the pure representation model. -/
theorem memo_lookup_correct (table : RustMemo) (left right : BalancedWord) :
    memo_lookup table left right = .ok (findResult table left right) := by
  induction table generalizing left right with
  | Empty => rw [memo_lookup]; rfl
  | Entry entry rest ih =>
    rw [memo_lookup, words_equal_correct, bind_ok]
    by_cases hl : left = entry.left <;> by_cases hr : right = entry.right
    all_goals simp [hl, hr, words_equal_correct, bind_ok, copy_result_correct, ih, findResult]

/-- Any real lookup hit from a sound table is a certified witness for the query. -/
theorem findResult_sound {table : RustMemo} (hs : TableSound table) {left right : BalancedWord}
    {result : verified_ordered_core.CommonEmbedding} (hfind : findResult table left right = some result) :
    Consistent left right result := by
  induction table with
  | Empty => simp [findResult] at hfind
  | Entry entry rest ih =>
    simp only [findResult] at hfind
    split at hfind
    · rename_i hkey
      have heq := Option.some.inj hfind
      rw [← heq, hkey.1, hkey.2]
      exact hs.1
    · exact ih hs.2 hfind

/-- The translated insertion copies exactly the key and result and prepends it. -/
theorem memo_insert_correct (table : RustMemo) (left right : BalancedWord)
    (result : verified_ordered_core.CommonEmbedding) :
    memo_insert table left right result =
      .ok (.Entry ⟨left, right, result⟩ table) := by
  rw [memo_insert, copy_word_correct, bind_ok, copy_word_correct, bind_ok,
    copy_result_correct, bind_ok]

theorem TableSound.insert {table : RustMemo} (hs : TableSound table) {left right : BalancedWord}
    {result : verified_ordered_core.CommonEmbedding} (hr : Consistent left right result) :
    TableSound (.Entry ⟨left, right, result⟩ table) := ⟨hr, hs⟩


/-- Forget cached tree witnesses but preserve exactly the numeric memo order. -/
def numericMemo : RustMemo → Paper2004.OrderedTree.MemoTable
  | .Empty => []
  | .Entry entry rest => ((toDyck entry.left, toDyck entry.right), entry.result.edges.val) :: numericMemo rest

/-- Cached tree correctness entails the independent numeric memo invariant. -/
theorem numericMemo_sound {table : RustMemo} (hs : TableSound table) :
    Paper2004.OrderedTree.MemoSound (numericMemo table) := by
  induction table with
  | Empty => intro entry he; simp [numericMemo] at he
  | Entry entry rest ih =>
    apply Paper2004.OrderedTree.MemoSound.cons (ih hs.2)
    calc
      entry.result.edges.val = (toDyck entry.result.word).semilength := hs.1.2
      _ = (paperCommon (toDyck entry.left) (toDyck entry.right)).semilength := congrArg DyckWord.semilength hs.1.1
      _ = paperLcs (toDyck entry.left) (toDyck entry.right) := (paperLcs_eq_witness _ _).symm

/-- The actual structural query and the numeric model have identical hits. -/
theorem numericMemo_lookup (table : RustMemo) (left right : BalancedWord) :
    (findResult table left right).map (fun result => result.edges.val) =
      Paper2004.OrderedTree.memoLookup (toDyck left, toDyck right) (numericMemo table) := by
  induction table generalizing left right with
  | Empty => rfl
  | Entry entry rest ih =>
    by_cases hl : left = entry.left <;> by_cases hr : right = entry.right
    all_goals simp [findResult, numericMemo, Paper2004.OrderedTree.memoLookup,
      Prod.mk.injEq, toDyck_eq_iff, hl, hr, ih]
/-- The real Rust memoized computation terminates, returns the independently
certified optimum, and preserves the meaning of all cached witnesses. -/
theorem memoized_common_embedding_refines (left right : BalancedWord) (table : RustMemo)
    (hs : TableSound table) (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ (result : verified_ordered_core.CommonEmbedding) (output : RustMemo),
      memoized_common_embedding left right table = .ok (some result, output) ∧
      Consistent left right result ∧ TableSound output ∧
      numericMemo output = (Paper2004.OrderedTree.memoLcs (toDyck left) (toDyck right) (numericMemo table)).table := by
  rw [verified_ordered_core.memoized_common_embedding.eq_def, memo_lookup_correct, bind_ok]
  cases hfind : findResult table left right with
  | some cached =>
    refine ⟨cached, table, rfl, findResult_sound hs hfind, hs, ?_⟩
    have hn : Paper2004.OrderedTree.memoLookup (toDyck left, toDyck right) (numericMemo table) =
        some cached.edges.val := by rw [← numericMemo_lookup, hfind]; rfl
    exact (memoLcs_hit_table _ _ _ _ hn).symm
  | none =>
    have hn : Paper2004.OrderedTree.memoLookup (toDyck left, toDyck right) (numericMemo table) = none := by
      rw [← numericMemo_lookup, hfind]
      rfl
    cases left with
    | Empty =>
      let result : verified_ordered_core.CommonEmbedding := ⟨.Empty, 0#u32⟩
      have hc : Consistent .Empty right result := ⟨by simp [result, toDyck], rfl⟩
      refine ⟨result, .Entry ⟨.Empty, right, result⟩ table, ?_, hc, hs.insert hc, ?_⟩
      · simp only [memo_insert_correct, bind_ok]
        rfl
      · rw [Paper2004.OrderedTree.memoLcs]
        simp only [memoFind_value, hn]
        rfl
    | Pair lh lt =>
      cases right with
      | Empty =>
        let result : verified_ordered_core.CommonEmbedding := ⟨.Empty, 0#u32⟩
        have hc : Consistent (.Pair lh lt) .Empty result := ⟨by simp [result, toDyck], rfl⟩
        refine ⟨result, .Entry ⟨.Pair lh lt, .Empty, result⟩ table, ?_, hc, hs.insert hc, ?_⟩
        · simp only [memo_insert_correct, bind_ok]
          rfl
        · rw [Paper2004.OrderedTree.memoLcs]
          simp only [memoFind_value]
          rw [hn]
          simp only [toDyck, Paper2004.BalancedDecomposition.nest_add_ne_zero, ↓reduceDIte]
          rfl
      | Pair rh rt =>
        have hlSize := hl
        have hrSize := hr
        simp only [toDyck, DyckWord.semilength_add, DyckWord.semilength_nest] at hlSize hrSize
        obtain ⟨heads, tableH, hheadsRun, ⟨hheadsWord, hheadsScore⟩, hsH, hnumH⟩ :=
          memoized_common_embedding_refines lh rh table hs (by omega) (by omega)
        obtain ⟨tails, tableT, htailsRun, ⟨htailsWord, htailsScore⟩, hsT, hnumT⟩ :=
          memoized_common_embedding_refines lt rt tableH hsH (by omega) (by omega)
        have hheadBound : heads.edges.val ≤ (toDyck lh).semilength := by
          rw [hheadsScore, hheadsWord]
          exact dyckEmbeds_semilength_le (paperCommon_sound _ _).1
        have htailBound : tails.edges.val ≤ (toDyck lt).semilength := by
          rw [htailsScore, htailsWord]
          exact dyckEmbeds_semilength_le (paperCommon_sound _ _).1
        obtain ⟨subtotal, hsum, hsubtotal⟩ := checked_add_success heads.edges tails.edges (by omega)
        obtain ⟨total, htotalRun, htotal⟩ := checked_add_success subtotal 1#u32 (by scalar_tac)
        obtain ⟨dropLeft, tableDL, hdropLeftRun, ⟨hdropLeftWord, hdropLeftScore⟩, hsDL, hnumDL⟩ :=
          memoized_common_embedding_refines (appendWord lh lt) (.Pair rh rt) tableT hsT
            (by simp only [toDyck_appendWord, DyckWord.semilength_add]; omega) hr
        obtain ⟨dropRight, tableDR, hdropRightRun, ⟨hdropRightWord, hdropRightScore⟩, hsDR, hnumDR⟩ :=
          memoized_common_embedding_refines (.Pair lh lt) (appendWord rh rt) tableDL hsDL hl
            (by simp only [toDyck_appendWord, DyckWord.semilength_add]; omega)
        let matched : verified_ordered_core.CommonEmbedding := ⟨.Pair heads.word tails.word, total⟩
        have hmatchedScore : matched.edges.val = (toDyck matched.word).semilength := by
          dsimp only [matched, toDyck]
          simp only [DyckWord.semilength_add, DyckWord.semilength_nest]
          have hone : (1#u32).val = 1 := rfl
          omega
        have hmatchedWord : toDyck matched.word =
            (paperCommon (toDyck lh) (toDyck rh)).nest + paperCommon (toDyck lt) (toDyck rt) := by
          simp only [matched, toDyck, hheadsWord, htailsWord]
        have hfirstScore := selectResult_score matched dropLeft hmatchedScore hdropLeftScore
        let result := selectResult (selectResult matched dropLeft) dropRight
        have hc : Consistent (.Pair lh lt) (.Pair rh rt) result := by
          constructor
          · calc
              toDyck result.word = longer (toDyck (selectResult matched dropLeft).word) (toDyck dropRight.word) :=
                selectResult_word _ _ hfirstScore hdropRightScore
              _ = longer (longer (toDyck matched.word) (toDyck dropLeft.word)) (toDyck dropRight.word) := by
                rw [selectResult_word matched dropLeft hmatchedScore hdropLeftScore]
              _ = paperCommon (toDyck (.Pair lh lt)) (toDyck (.Pair rh rt)) := by
                rw [hmatchedWord, hdropLeftWord, hdropRightWord, toDyck_appendWord, toDyck_appendWord]
                exact (paperCommon_nest_add _ _ _ _).symm
          · exact selectResult_score _ _ hfirstScore hdropRightScore
        refine ⟨result, .Entry ⟨.Pair lh lt, .Pair rh rt, result⟩ tableDR, ?_, hc, hsDR.insert hc, ?_⟩
        · simp only [hheadsRun, htailsRun, bind_ok, uncurry_apply_pair, lift, hsum, htotalRun,
            concatenate_correct, hdropLeftRun, hdropRightRun, choose_longer_correct, memo_insert_correct]
          rfl
        · have hvalue : result.edges.val = paperLcs (toDyck (.Pair lh lt)) (toDyck (.Pair rh rt)) := by
            rw [hc.2, hc.1, paperLcs_eq_witness]
          rw [numericMemo, hvalue, hnumDR, hnumDL, hnumT, hnumH]
          have hm := memoLcs_miss_table (toDyck (.Pair lh lt)) (toDyck (.Pair rh rt))
            (numericMemo table) (numericMemo_sound hs) hn
            (Paper2004.BalancedDecomposition.nest_add_ne_zero _ _)
            (Paper2004.BalancedDecomposition.nest_add_ne_zero _ _)
          simpa only [toDyck, DyckWord.insidePart_add DyckWord.nest_ne_zero,
            DyckWord.outsidePart_add DyckWord.nest_ne_zero, DyckWord.insidePart_nest,
            DyckWord.outsidePart_nest, zero_add, toDyck_appendWord] using hm.symm
termination_by (toDyck left).semilength + (toDyck right).semilength
decreasing_by
  all_goals subst_vars
  all_goals simp only [toDyck_appendWord, toDyck, DyckWord.semilength_add, DyckWord.semilength_nest]
  all_goals omega

/-- The actual memoized Rust entry point, starting from an empty cache,
returns an independently optimal tree with an exact score. -/
theorem maximum_common_embedding_correct (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ result : verified_ordered_core.CommonEmbedding,
      maximum_common_embedding left right = .ok (some result) ∧
      IsMaximumCommon (decodeDyck (toDyck result.word)) (decodeDyck (toDyck left)) (decodeDyck (toDyck right)) ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  obtain ⟨result, output, hrun, ⟨hword, hscore⟩, _⟩ :=
    memoized_common_embedding_refines left right .Empty trivial hl hr
  refine ⟨result, ?_, ?_, ?_⟩
  · rw [maximum_common_embedding, hrun, bind_ok]
    rfl
  · apply longestCommonBalanced_decodes_maximum
    simpa only [encodeDyck_decodeDyck, hword] using paperCommon_correct (toDyck left) (toDyck right)
  · have hsize := encodeDyck_semilength (decodeDyck (toDyck result.word))
    rw [encodeDyck_decodeDyck] at hsize
    omega

/-- The number of real Rust cache records, independently of their payload size. -/
def memoLength : RustMemo → Nat
  | .Empty => 0
  | .Entry _ rest => memoLength rest + 1

@[simp] theorem numericMemo_length (table : RustMemo) : (numericMemo table).length = memoLength table := by
  induction table with
  | Empty => rfl
  | Entry entry rest ih => simp only [numericMemo, List.length_cons, ih, memoLength]

/-- Exact refinement of the updated Rust cache transfers the independently
proved finite state bound and absence of duplicate keys to real Rust execution. -/
theorem memoized_common_embedding_cache_bound (left right : BalancedWord)
    (hl : (toDyck left).semilength < 2^32) (hr : (toDyck right).semilength < 2^32) :
    ∃ (result : verified_ordered_core.CommonEmbedding) (output : RustMemo),
      memoized_common_embedding left right .Empty = .ok (some result, output) ∧
      Consistent left right result ∧
      memoLength output ≤ (Paper2004.BalancedDecomposition.states (toDyck left)).card *
        (Paper2004.BalancedDecomposition.states (toDyck right)).card ∧
      ((numericMemo output).map Prod.fst).Nodup := by
  obtain ⟨result, output, hrun, hc, _, hn⟩ := memoized_common_embedding_refines left right .Empty trivial hl hr
  change numericMemo output = (Paper2004.OrderedTree.memoLcs (toDyck left) (toDyck right) []).table at hn
  refine ⟨result, output, hrun, hc, ?_, ?_⟩
  · have hb := memoLcs_table_bound (toDyck left) (toDyck right)
    rw [← hn] at hb
    simpa only [numericMemo_length] using hb
  · rw [hn]
    exact memoLcs_nodup (toDyck left) (toDyck right) [] (by simp)

/-- Arbitrary independent tree inputs are covered by the actual memoized entry
point; no caller-supplied cache invariant is required. -/
theorem maximum_common_embedding_of_trees (left right : Paper2004.OrderedTree)
    (hl : left.edgeCount < 2^32) (hr : right.edgeCount < 2^32) :
    ∃ result : verified_ordered_core.CommonEmbedding,
      maximum_common_embedding (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) = .ok (some result) ∧
      IsMaximumCommon (decodeDyck (toDyck result.word)) left right ∧
      result.edges.val = (decodeDyck (toDyck result.word)).edgeCount := by
  have hlrep : (toDyck (fromDyck left.encodeDyck)).semilength < 2^32 := by
    simpa only [toDyck_fromDyck, encodeDyck_semilength] using hl
  have hrrep : (toDyck (fromDyck right.encodeDyck)).semilength < 2^32 := by
    simpa only [toDyck_fromDyck, encodeDyck_semilength] using hr
  simpa only [toDyck_fromDyck, decodeDyck_encodeDyck] using
    maximum_common_embedding_correct (fromDyck left.encodeDyck) (fromDyck right.encodeDyck) hlrep hrrep

end SubtreeProofs.Rust.MemoizedOrderedSolver

end
