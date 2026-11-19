module

public import SubtreeProofs.Rust.SourcePairRootSubtotal

/-! Open native total-score storage and copy the retained subtotal into the
actual single scalar argument for checked addition of the literal one. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

structure RootScoreArgumentScope (heads tails : CommonEmbedding) (table : MemoTable) (subtotal : Aeneas.Std.U32)
    (world : World) (active : Activation) : Prop where
  headValue : active.state 37 = Slot.ofValue (encodeResult heads)
  tailValue : active.state 47 = Slot.ofValue (encodeResult tails)
  tableValue : active.state 42 = Slot.ofValue (encodeTable table)
  subtotalValue : active.state 51 = .number subtotal.val
  argument : active.state 60 = .number subtotal.val
  totalEmpty : active.state 58 = .empty
  totalRoot : ∃ binding, active.roots 58 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  resultEmpty : active.state 59 = .empty
  resultRoot : ∃ binding, active.roots 59 = some binding ∧ world.memory[binding.address]? = some (.node .tuple 0 [])
  argumentRoot : ∃ binding, active.roots 60 = some binding
  retired : ∀ slot ∈ [52, 55], active.roots slot = none

theorem pair_root_score_arguments_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] world active)
    (callee : Derived.Callees) {heads tails : CommonEmbedding} {table : MemoTable} {subtotal : Aeneas.Std.U32}
    (scope : RootSubtotalScope heads tails table subtotal active)
    (count : 61 ≤ active.count) (unbound : ∀ slot ∈ [58, 59, 60], active.roots slot = none) :
    ∃ final after,
      Calling.Prefix callee callers (rootScoreCode 10) ((rootScoreActions.drop 6).take 4) world active final after ∧
      OriginalLoanMachine before callers previous external [45, 44, 35, 34, 30, 29, 28, 27, 1, 2, 13] final after ∧
      RootScoreArgumentScope heads tails table subtotal final after ∧ after.count = active.count ∧ after.frame = active.frame ∧
      (∀ slot, slot ∉ [58, 59, 60] → after.roots slot = active.roots slot) ∧
      (∀ index binding, active.roots index = some binding → ∀ raw,
        world.memory[binding.address]? = some raw → final.memory[binding.address]? = some raw) := by
  obtain ⟨w58, a58, run58, m58, roots58, count58, frame58, empty58, raw58, memory58⟩ :=
    original_open_local_complete h callee (rootScoreCode 7) (slot := 58) (by decide) (by omega) (unbound 58 (by simp))
  obtain ⟨w59, a59, run59, m59, roots59, count59, frame59, empty59, raw59, memory59⟩ :=
    original_open_local_complete m58 callee (rootScoreCode 8) (slot := 59) (by decide) (by rw [count58]; omega)
      (by simpa [roots58, Roots.set] using unbound 59 (by simp))
  have first2 : Calling.Prefix callee callers (rootScoreCode 8) ((rootScoreActions.drop 6).take 2) world active w59 a59 :=
    Calling.Prefix.append (suffix := rootScoreCode 8) (rest := [.storageLive 59]) run58 run59
  have subtotal59 : a59.state 51 = .number subtotal.val :=
    (first2.closed_local_same (index := 51) h.native.valid h.native.callersValid h.native.wellFormed
      (by rw [scope.subtotalValue]; exact .number subtotal.hmax) .u32 (by decide +kernel) (by decide +kernel)).trans scope.subtotalValue
  obtain ⟨final, after, run60, machine, roots60, count60, frame60, subtotal60, value60, memory60⟩ :=
    original_number_copy_complete m59 callee (rootScoreCode 10) (source := 51) (destination := 60) (by decide) (by decide) (by decide)
      subtotal59 (.local 51) rfl (number_local_read subtotal.val) subtotal.hmax (by rw [count59, count58]; omega)
      (by simpa [roots59, roots58, Roots.set] using unbound 60 (by simp))
  have whole : Calling.Prefix callee callers (rootScoreCode 10) ((rootScoreActions.drop 6).take 4) world active final after :=
    Calling.Prefix.append (suffix := rootScoreCode 10) (rest := (rootScoreActions.drop 8).take 2) first2 run60
  let root58 : Binding := ⟨world.memory.length, world.memory.length⟩
  let root59 : Binding := ⟨w58.memory.length, w58.memory.length⟩
  have bound58a58 : a58.roots 58 = some root58 := by simp [root58, roots58, Roots.set]
  have bound58a59 : a59.roots 58 = some root58 := by simpa [roots59, Roots.set] using bound58a58
  have bound59a59 : a59.roots 59 = some root59 := by simp [root59, roots59, Roots.set]
  have last3 : Calling.Prefix callee callers (rootScoreCode 10) ((rootScoreActions.drop 7).take 3) w58 a58 final after :=
    Calling.Prefix.append (suffix := rootScoreCode 10) (rest := (rootScoreActions.drop 8).take 2) run59 run60
  refine ⟨final, after, whole, machine, ?_, count60.trans (count59.trans count58), frame60.trans (frame59.trans frame58), ?_, ?_⟩
  · refine ⟨?_, ?_, ?_, subtotal60, value60, ?_,
      ⟨root58, by simpa [roots60, Roots.set] using bound58a59, memory60 58 root58 bound58a59 _ (memory59 58 root58 bound58a58 _ raw58)⟩, ?_,
      ⟨root59, by simpa [roots60, Roots.set] using bound59a59, memory60 59 root59 bound59a59 _ raw59⟩,
      ⟨⟨w59.memory.length, w59.memory.length⟩, by simp [roots60, Roots.set]⟩, ?_⟩
    · exact (whole.closed_local_same (index := 37) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.headValue]; exact ofValue_typed (result_typed heads)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.headValue
    · exact (whole.closed_local_same (index := 47) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tailValue]; exact ofValue_typed (result_typed tails)) (.adt .embedding) (by decide +kernel) (by decide +kernel)).trans scope.tailValue
    · exact (whole.closed_local_same (index := 42) h.native.valid h.native.callersValid h.native.wellFormed
        (by rw [scope.tableValue]; exact ofValue_typed (table_typed table)) (.adt .table) (by decide +kernel) (by decide +kernel)).trans scope.tableValue
    · exact (last3.closed_local_same (index := 58) m58.native.valid m58.native.callersValid m58.native.wellFormed
        (by rw [empty58]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty58
    · exact (run60.closed_local_same (index := 59) m59.native.valid m59.native.callersValid m59.native.wellFormed
        (by rw [empty59]; exact .empty .u32) .u32 (by decide +kernel) (by decide +kernel)).trans empty59
    · intro slot member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl <;> simp only [roots60, roots59, roots58, Roots.set] <;> exact scope.retired _ (by simp)
  · intro slot outside
    have different : slot ≠ 58 ∧ slot ≠ 59 ∧ slot ≠ 60 := by simpa using outside
    simp only [roots60, roots59, roots58, Roots.set, different.1, different.2.1, different.2.2, ite_false]
  · intro index binding root raw memoryRead
    have not58 : index ≠ 58 := by intro same; subst index; rw [unbound 58 (by simp)] at root; cases root
    have not59 : index ≠ 59 := by intro same; subst index; rw [unbound 59 (by simp)] at root; cases root
    have rootA58 : a58.roots index = some binding := by simpa only [roots58, Roots.set, not58, ite_false] using root
    have rootA59 : a59.roots index = some binding := by simpa only [roots59, Roots.set, not59, ite_false] using rootA58
    exact memory60 index binding rootA59 _ (memory59 index binding rootA58 _ (memory58 index binding root _ memoryRead))

end SubtreeProofs.Rust.SourceEval.Evaluator
