module

public import SubtreeProofs.Rust.SourcePairScoreProgram
public import SubtreeProofs.Rust.SourceOriginalOpenLocal
public import SubtreeProofs.Rust.SourceOriginalNumberView

/-! Prepare the actual subtotal call: open result and subtotal locals,
then copy both native edge counts without transferring their witness owners. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

theorem result_score_read (result : CommonEmbedding) :
    (Slot.ofValue (encodeResult result)).read [.field none 1] = some (.number result.edges.val) := by
  simp [encodeResult, Slot.ofValue, ofFields, Slot.read, Slot.get, Slot.materialize]

structure ScoreArgumentScope (initial : Activation) (heads tails : CommonEmbedding) (table : MemoTable)
    (world : World) (active : Activation) : Prop where
  count : active.count = initial.count
  frame : active.frame = initial.frame
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  table : active.state 42 = Slot.ofValue (encodeTable table)
  left : active.state 53 = .number heads.edges.val
  right : active.state 54 = .number tails.edges.val
  resultEmpty : active.state 52 = .empty
  resultRoot : ∃ binding, active.roots 52 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  subtotalEmpty : active.state 51 = .empty
  subtotalRoot : ∃ binding, active.roots 51 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  bound : ∀ slot ∈ [51, 52, 53, 54], ∃ binding, active.roots slot = some binding
  otherRoots : ∀ slot, slot ∉ [51, 52, 53, 54] → active.roots slot = initial.roots slot

theorem pair_score_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable}
    (headValue : active.state 37 = Slot.ofValue (encodeResult heads))
    (tailValue : active.state 47 = Slot.ofValue (encodeResult tails))
    (tableValue : active.state 42 = Slot.ofValue (encodeTable table))
    (count : 55 ≤ active.count) (unbound : ∀ slot ∈ [51, 52, 53, 54], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (scoreCode 12) ((scoreActions.drop 6).take 6) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      ScoreArgumentScope active heads tails table final after ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w51, a51, run51, m51, roots51, count51, frame51, empty51, raw51, memory51⟩ :=
    original_open_local_complete h callee (scoreCode 7) (slot := 51) (by decide) (by omega) (unbound 51 (by simp))
  obtain ⟨w52, a52, run52, m52, roots52, count52, frame52, empty52, raw52, memory52⟩ :=
    original_open_local_complete m51 callee (scoreCode 8) (slot := 52) (by decide) (by rw [count51]; omega)
      (by simpa [roots51, Roots.set] using unbound 52 (by simp))
  have first2 : Calling.Prefix callee callers (scoreCode 8) ((scoreActions.drop 6).take 2) world active w52 a52 :=
    Calling.Prefix.append (suffix := scoreCode 8) (rest := [.storageLive 52]) run51 run52
  have heads52 : a52.state 37 = Slot.ofValue (encodeResult heads) :=
    (first2.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [headValue]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans headValue
  obtain ⟨w53, a53, run53, m53, roots53, count53, frame53, heads53, value53, memory53⟩ :=
    original_number_copy_complete m52 callee (scoreCode 10) (source := 37) (destination := 53) (by decide) (by decide) (by decide)
      heads52 (.field (.local 37) none 1) rfl (result_score_read heads) heads.edges.hmax
      (by rw [count52, count51]; omega) (by simpa [roots52, roots51, Roots.set] using unbound 53 (by simp))
  have first4 : Calling.Prefix callee callers (scoreCode 10) ((scoreActions.drop 6).take 4) world active w53 a53 :=
    Calling.Prefix.append (suffix := scoreCode 10) (rest := (scoreActions.drop 8).take 2) first2 run53
  have tails53 : a53.state 47 = Slot.ofValue (encodeResult tails) :=
    (first4.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [tailValue]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans tailValue
  obtain ⟨final, after, run54, machine, roots54, count54, frame54, tails54, value54, memory54⟩ :=
    original_number_copy_complete m53 callee (scoreCode 12) (source := 47) (destination := 54) (by decide) (by decide) (by decide)
      tails53 (.field (.local 47) none 1) rfl (result_score_read tails) tails.edges.hmax
      (by rw [count53, count52, count51]; omega) (by simpa [roots53, roots52, roots51, Roots.set] using unbound 54 (by simp))
  have whole : Calling.Prefix callee callers (scoreCode 12) ((scoreActions.drop 6).take 6) world active final after :=
    Calling.Prefix.append (suffix := scoreCode 12) (rest := (scoreActions.drop 10).take 2) first4 run54
  let root51 : Binding := ⟨world.memory.length, world.memory.length⟩
  let root52 : Binding := ⟨w51.memory.length, w51.memory.length⟩
  have bound51a51 : a51.roots 51 = some root51 := by simp [root51, roots51, Roots.set]
  have bound51a52 : a52.roots 51 = some root51 := by simpa [roots52, Roots.set] using bound51a51
  have bound51a53 : a53.roots 51 = some root51 := by simpa [roots53, Roots.set] using bound51a52
  have bound52a52 : a52.roots 52 = some root52 := by simp [root52, roots52, Roots.set]
  have bound52a53 : a53.roots 52 = some root52 := by simpa [roots53, Roots.set] using bound52a52
  have rest4 : Calling.Prefix callee callers (scoreCode 12) ((scoreActions.drop 8).take 4) w52 a52 final after :=
    Calling.Prefix.append (suffix := scoreCode 12) (rest := (scoreActions.drop 10).take 2) run53 run54
  have rest5 : Calling.Prefix callee callers (scoreCode 12) ((scoreActions.drop 7).take 5) w51 a51 final after :=
    Calling.Prefix.append (suffix := scoreCode 12) (rest := (scoreActions.drop 8).take 4) run52 rest4
  refine ⟨final, after, whole, machine, ?_, ?_⟩
  · refine ⟨count54.trans (count53.trans (count52.trans count51)), frame54.trans (frame53.trans (frame52.trans frame51)), ?_, tails54, ?_, ?_, value54, ?_,
      ⟨root52, by simpa [roots54, Roots.set] using bound52a53, memory54 52 root52 bound52a53 _ (memory53 52 root52 bound52a52 _ raw52)⟩, ?_,
      ⟨root51, by simpa [roots54, Roots.set] using bound51a53, memory54 51 root51 bound51a53 _ (memory53 51 root51 bound51a52 _ (memory52 51 root51 bound51a51 _ raw51))⟩, ?_, ?_⟩
    · exact (whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [headValue]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans headValue
    · exact (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans tableValue
    · exact (run54.closed_local_same (index := 53) m53.native.valid m53.native.callersValid m53.native.wellFormed
        (by rw [value53]; exact .number heads.edges.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans value53
    · exact (rest4.closed_local_same (index := 52) m52.native.valid m52.native.callersValid m52.native.wellFormed
        (by rw [empty52]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty52
    · exact (rest5.closed_local_same (index := 51) m51.native.valid m51.native.callersValid m51.native.wellFormed
        (by rw [empty51]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty51
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl <;> simp [roots54, roots53, roots52, roots51, Roots.set]
    · intro slot outside
      have different : slot ≠ 51 ∧ slot ≠ 52 ∧ slot ≠ 53 ∧ slot ≠ 54 := by simpa using outside
      simp only [roots54, roots53, roots52, roots51, Roots.set, different.1, different.2.1, different.2.2.1, different.2.2.2, ite_false]
  · intro index binding root raw memoryRead
    have not51 : index ≠ 51 := by intro same; subst index; rw [unbound 51 (by simp)] at root; cases root
    have not52 : index ≠ 52 := by intro same; subst index; rw [unbound 52 (by simp)] at root; cases root
    have not53 : index ≠ 53 := by intro same; subst index; rw [unbound 53 (by simp)] at root; cases root
    have rootA51 : a51.roots index = some binding := by simpa only [roots51, Roots.set, not51, ite_false] using root
    have rootA52 : a52.roots index = some binding := by simpa only [roots52, Roots.set, not52, ite_false] using rootA51
    have rootA53 : a53.roots index = some binding := by simpa only [roots53, Roots.set, not53, ite_false] using rootA52
    exact memory54 index binding rootA53 _ (memory53 index binding rootA52 _ (memory52 index binding rootA51 _ (memory51 index binding root _ memoryRead)))

end SubtreeProofs.Rust.SourceEval.Evaluator
