module

public import SubtreeProofs.Rust.LookupHeapTyping

/-! Constructive layouts for arbitrary existing Rust/Aeneas input values.
These build a represented initial heap, not an uncharged input-conversion step
inside lookup. Setup/materialization costs remain outside the lookup contract. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Heap

open verified_ordered_core

def packWord : BalancedWord → Memory → Cell × Memory
  | .Empty, memory => (.node .word 0 [], memory)
  | .Pair head tail, memory =>
    let (head, memory) := packWord head memory
    let (head, memory) := alloc memory head
    let (tail, memory) := packWord tail memory
    let (tail, memory) := alloc memory tail
    (.node .word 1 [head, tail], memory)

theorem packWord_spec (word : BalancedWord) (memory : Memory) :
    Represents (packWord word memory).2 (packWord word memory).1 (encodeWord word) ∧
      Extends memory (packWord word memory).2 := by
  induction word generalizing memory with
  | Empty => exact ⟨.node .nil, .refl memory⟩
  | Pair head tail ihHead ihTail =>
    generalize hh : packWord head memory = ph at *
    cases ph with
    | mk ch mh =>
      have hhead := ihHead memory
      rw [hh] at hhead
      obtain ⟨ht, hte⟩ := ihTail (mh ++ [ch])
      generalize htcall : packWord tail (mh ++ [ch]) = pt at *
      cases pt with
      | mk ct mt =>
        dsimp only [Prod.fst, Prod.snd] at hhead ht hte
        simp only [packWord, hh, alloc, htcall]
        change Represents (mt ++ [ct])
          (.node .word 1 [.owned mh.length, .owned mt.length])
          (.node .word 1 [.boxed (encodeWord head), .boxed (encodeWord tail)]) ∧
          Extends memory (mt ++ [ct])
        have he := hte.trans (Extends.append mt [ct])
        exact ⟨.node (.cons ((alloc_rep hhead.1).mono he) (.cons (alloc_rep ht) .nil)),
          (hhead.2.trans (Extends.append mh [ch])).trans he⟩

def packResult (value : CommonEmbedding) (memory : Memory) : Cell × Memory :=
  let (word, memory) := packWord value.word memory
  (.node .embedding 0 [word, .number value.edges.val], memory)

theorem packResult_spec (value : CommonEmbedding) (memory : Memory) :
    Represents (packResult value memory).2 (packResult value memory).1 (encodeResult value) ∧
      Extends memory (packResult value memory).2 := by
  have h := packWord_spec value.word memory
  exact ⟨.node (.cons h.1 (.cons (.number _) .nil)), h.2⟩

def packEntry (value : MemoEntry) (memory : Memory) : Cell × Memory :=
  let (left, memory) := packWord value.left memory
  let (right, memory) := packWord value.right memory
  let (result, memory) := packResult value.result memory
  (.node .entry 0 [left, right, result], memory)

theorem packEntry_spec (value : MemoEntry) (memory : Memory) :
    Represents (packEntry value memory).2 (packEntry value memory).1
      (.node .entry 0 [encodeWord value.left, encodeWord value.right, encodeResult value.result]) ∧
      Extends memory (packEntry value memory).2 := by
  have hl := packWord_spec value.left memory
  have hr := packWord_spec value.right (packWord value.left memory).2
  have hc := packResult_spec value.result (packWord value.right (packWord value.left memory).2).2
  exact ⟨.node (.cons (hl.1.mono (hr.2.trans hc.2)) (.cons (hr.1.mono hc.2) (.cons hc.1 .nil))),
    hl.2.trans (hr.2.trans hc.2)⟩

def packTable : MemoTable → Memory → Cell × Memory
  | .Empty, memory => (.node .table 0 [], memory)
  | .Entry entry rest, memory =>
    let (entry, memory) := packEntry entry memory
    let (entry, memory) := alloc memory entry
    let (rest, memory) := packTable rest memory
    let (rest, memory) := alloc memory rest
    (.node .table 1 [entry, rest], memory)

theorem packTable_spec (table : MemoTable) (memory : Memory) :
    Represents (packTable table memory).2 (packTable table memory).1 (encodeTable table) ∧
      Extends memory (packTable table memory).2 := by
  induction table generalizing memory with
  | Empty => exact ⟨.node .nil, .refl memory⟩
  | Entry entry rest ih =>
    have he := packEntry_spec entry memory
    generalize hentry : packEntry entry memory = pe at *
    cases pe with
    | mk ce me =>
      obtain ⟨hr, hre⟩ := ih (me ++ [ce])
      generalize hrest : packTable rest (me ++ [ce]) = pr at *
      cases pr with
      | mk cr mr =>
        dsimp only [Prod.fst, Prod.snd] at he hr hre
        simp only [packTable, hentry, alloc, hrest]
        change Represents (mr ++ [cr])
          (.node .table 1 [.owned me.length, .owned mr.length]) _ ∧
          Extends memory (mr ++ [cr])
        have hex := hre.trans (Extends.append mr [cr])
        exact ⟨.node (.cons ((alloc_rep he.1).mono hex) (.cons (alloc_rep hr) .nil)),
          (he.2.trans (Extends.append me [ce])).trans hex⟩

def shareRoot (memory : Memory) (value : Cell) : Cell × Memory :=
  (.shared ⟨memory.length, []⟩, memory ++ [value])

theorem shareRoot_spec {memory : Memory} {cell : Cell} {value : Value}
    (h : Represents memory cell value) :
    Represents (shareRoot memory cell).2 (shareRoot memory cell).1 (.reference value) ∧
      Extends memory (shareRoot memory cell).2 := by
  have he := Extends.append memory [cell]
  refine ⟨.shared ?_ (h.mono he), he⟩
  simp [shareRoot, read, fields]

/-- The input-representation premise of heap lookup is inhabited for every
native table and query, while preserving any existing immutable heap. -/
theorem inputs_exist (table : MemoTable) (left right : BalancedWord) (memory : Memory) :
    ∃ args after, RepresentsFields after args
      [.reference (encodeTable table), .reference (encodeWord left), .reference (encodeWord right)] ∧
      Extends memory after := by
  have ht := packTable_spec table memory
  have hts := shareRoot_spec ht.1
  have hl := packWord_spec left (shareRoot (packTable table memory).2 (packTable table memory).1).2
  have hls := shareRoot_spec hl.1
  have hr := packWord_spec right
    (shareRoot (packWord left (shareRoot (packTable table memory).2 (packTable table memory).1).2).2
      (packWord left (shareRoot (packTable table memory).2 (packTable table memory).1).2).1).2
  have hrs := shareRoot_spec hr.1
  refine ⟨_, _, .cons (hts.1.mono (hl.2.trans (hls.2.trans (hr.2.trans hrs.2))))
    (.cons (hls.1.mono (hr.2.trans hrs.2)) (.cons hrs.1 .nil)), ?_⟩
  exact ht.2.trans (hts.2.trans (hl.2.trans (hls.2.trans (hr.2.trans hrs.2))))

end SubtreeProofs.Rust.LookupSource.Heap
