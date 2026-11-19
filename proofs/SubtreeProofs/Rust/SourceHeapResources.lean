module

public import SubtreeProofs.Rust.SourceHeapGraphTrace
public import SubtreeProofs.Rust.SourceHeapTransport

/-! Concrete partial resource inventories distinguish complete read graphs,
exclusive-owner occurrences and shared-loan targets. An owned shell contributes
to reads/owners; it contributes to loans only through shared references inside
its initialized payload. All tracing is ghost interpretation bookkeeping. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open LookupSource.Heap

structure Resources where
  reads : List Nat := []
  owners : List Nat := []
  loans : List Nat := []
  deriving DecidableEq, Repr

def Resources.plus (a b : Resources) : Resources :=
  ⟨a.reads ++ b.reads, a.owners ++ b.owners, a.loans ++ b.loans⟩

def Resources.atRoot (r : Resources) (address : Nat) : Resources :=
  { r with reads := r.reads ++ [address] }

mutual
  inductive BorrowFootprint (memory : Memory) : Cell → Slot → List Nat → Prop where
    | empty (cell : Cell) : BorrowFootprint memory cell .empty []
    | boolean (b : Bool) : BorrowFootprint memory (.boolean b) (.boolean b) []
    | number (n : Nat) : BorrowFootprint memory (.number n) (.number n) []
    | node {kind : Kind} {tag : Nat} {cells : List Cell} {parts : List Slot} {loans : List Nat} :
        BorrowFields memory cells parts loans → BorrowFootprint memory (.node kind tag cells) (.node kind tag parts) loans
    | shared {pointer : Pointer} {value : Value} {loans : List Nat} :
        Graph memory (.shared pointer) (.reference value) loans → BorrowFootprint memory (.shared pointer) (.shared value) loans
    | owned {address : Nat} {cell : Cell} {part : Slot} {loans : List Nat} :
        memory[address]? = some cell → BorrowFootprint memory cell part loans →
        BorrowFootprint memory (.owned address) (.boxed part) loans

  inductive BorrowFields (memory : Memory) : List Cell → List Slot → List Nat → Prop where
    | nil : BorrowFields memory [] [] []
    | cons {cell : Cell} {part : Slot} {cells : List Cell} {parts : List Slot} {first rest : List Nat} :
        BorrowFootprint memory cell part first → BorrowFields memory cells parts rest →
        BorrowFields memory (cell :: cells) (part :: parts) (first ++ rest)
end

structure ResourceRep (memory : Memory) (cell : Cell) (part : Slot) (r : Resources) : Prop where
  graph : PartialGraph memory cell part r.reads
  owned : Rep memory cell part r.owners
  borrowed : BorrowFootprint memory cell part r.loans

structure FieldsResourceRep (memory : Memory) (cells : List Cell) (parts : List Slot) (r : Resources) : Prop where
  graph : PartialGraphFields memory cells parts r.reads
  owned : FieldsRep memory cells parts r.owners
  borrowed : BorrowFields memory cells parts r.loans

mutual
  def traceResources (memory : Memory) (cell : Cell) : Slot → Option Resources
    | .empty => some {}
    | .boolean b => match cell with
      | .boolean actual => if b = actual then some {} else none
      | _ => none
    | .number n => match cell with
      | .number actual => if n = actual then some {} else none
      | _ => none
    | .node kind tag parts => match cell with
      | .node actual variant cells =>
        if kind = actual ∧ tag = variant then traceFieldsResources memory cells parts else none
      | _ => none
    | .shared target => do
      let guards ← traceGraph memory cell (.reference target)
      some ⟨guards, [], guards⟩
    | .boxed part => match cell with
      | .owned address => do
        let child ← memory[address]?
        let r ← traceResources memory child part
        some ⟨r.reads ++ [address], r.owners ++ [address], r.loans⟩
      | _ => none
  termination_by part => sizeOf part

  def traceFieldsResources (memory : Memory) : List Cell → (parts : List Slot) → Option Resources
    | [], [] => some {}
    | cell :: cells, part :: parts => do
      let first ← traceResources memory cell part
      let rest ← traceFieldsResources memory cells parts
      some (first.plus rest)
    | _, _ => none
  termination_by _ parts => sizeOf parts
end

mutual
  theorem PartialGraph.resources {memory : Memory} {cell : Cell} {part : Slot} {guards : List Nat}
      (h : PartialGraph memory cell part guards) :
      ∃ r, traceResources memory cell part = some r ∧ r.reads = guards ∧ ResourceRep memory cell part r := by
    cases h with
    | empty cell => exact ⟨{}, by simp only [traceResources], rfl, .mk (.empty cell) (.empty cell) (.empty cell)⟩
    | boolean b => exact ⟨{}, by simp only [traceResources, ↓reduceIte], rfl, .mk (.boolean b) (.boolean b) (.boolean b)⟩
    | number n => exact ⟨{}, by simp only [traceResources, ↓reduceIte], rfl, .mk (.number n) (.number n) (.number n)⟩
    | shared hg =>
      exact ⟨⟨_, [], _⟩, by simp only [traceResources, hg.trace, Bind.bind, Option.bind], rfl,
        .mk (.shared hg) (.shared hg.represents) (.shared hg)⟩
    | node fields =>
      obtain ⟨r, hr, he, hv⟩ := fields.resources
      exact ⟨r, by simp only [traceResources, and_self, ↓reduceIte, hr], he,
        .mk (.node hv.graph) (.node hv.owned) (.node hv.borrowed)⟩
    | @owned address child part guards hr childGraph =>
      obtain ⟨r, hc, he, hv⟩ := childGraph.resources
      exact ⟨⟨r.reads ++ [address], r.owners ++ [address], r.loans⟩,
        by simp only [traceResources, hr, hc, Bind.bind, Option.bind], by simp only [he],
        .mk (.owned hr hv.graph) (.owned hr hv.owned) (.owned hr hv.borrowed)⟩

  theorem PartialGraphFields.resources {memory : Memory} {cells : List Cell} {parts : List Slot} {guards : List Nat}
      (h : PartialGraphFields memory cells parts guards) :
      ∃ r, traceFieldsResources memory cells parts = some r ∧ r.reads = guards ∧ FieldsResourceRep memory cells parts r := by
    cases h with
    | nil => exact ⟨{}, by simp only [traceFieldsResources], rfl, .mk .nil .nil .nil⟩
    | cons first rest =>
      obtain ⟨a, ha, he, hv⟩ := first.resources
      obtain ⟨b, hb, he', hv'⟩ := rest.resources
      exact ⟨a.plus b, by simp only [traceFieldsResources, ha, hb, Bind.bind, Option.bind],
        by simp only [Resources.plus, he, he'], .mk (.cons hv.graph hv'.graph) (.cons hv.owned hv'.owned)
          (.cons hv.borrowed hv'.borrowed)⟩
end

theorem ResourceRep.boxes {memory : Memory} {cell : Cell} {part : Slot} {r : Resources}
    (h : ResourceRep memory cell part r) : r.owners.length = part.dropWork.boxes := h.owned.boxes

mutual
  theorem BorrowFootprint.subset_reads {memory : Memory} {cell : Cell} {part : Slot} {loans reads : List Nat}
      (h : BorrowFootprint memory cell part loans) (hg : PartialGraph memory cell part reads) : loans ⊆ reads := by
    cases h with
    | empty _ | boolean _ | number _ => simp
    | node fields => cases hg with | node data => exact fields.subset_reads data
    | shared loan => cases hg with
      | shared data => rw [loan.guards_unique data]
    | owned hr child => cases hg with
      | owned hs data =>
        have he := Option.some.inj (hr.symm.trans hs)
        cases he
        exact fun _ ha => List.mem_append_left _ (child.subset_reads data ha)

  theorem BorrowFields.subset_reads {memory : Memory} {cells : List Cell} {parts : List Slot} {loans reads : List Nat}
      (h : BorrowFields memory cells parts loans) (hg : PartialGraphFields memory cells parts reads) : loans ⊆ reads := by
    cases h with
    | nil => simp
    | cons first rest => cases hg with
      | cons data tail =>
        intro address ha
        rcases List.mem_append.mp ha with ha | ha
        · exact List.mem_append_left _ (first.subset_reads data ha)
        · exact List.mem_append_right _ (rest.subset_reads tail ha)
end

mutual
  theorem BorrowFootprint.transport {before after : Memory} {cell : Cell} {part : Slot} {loans reads : List Nat}
      (h : BorrowFootprint before cell part loans) (hg : PartialGraph before cell part reads)
      (hk : Retains before after reads) : BorrowFootprint after cell part loans := by
    cases h with
    | empty cell => exact .empty cell
    | boolean b => exact .boolean b
    | number n => exact .number n
    | node fields => cases hg with | node data => exact .node (fields.transport data hk)
    | shared loan => cases hg with
      | shared data =>
        have he := loan.guards_unique data
        exact .shared (loan.transport (by simpa only [he] using hk))
    | owned hr child => cases hg with
      | owned hs data =>
        have he := Option.some.inj (hr.symm.trans hs)
        cases he
        exact .owned (hk _ (List.mem_append_right _ (by simp)) _ hr)
          (child.transport data (hk.weaken (fun _ ha => List.mem_append_left _ ha)))

  theorem BorrowFields.transport {before after : Memory} {cells : List Cell} {parts : List Slot} {loans reads : List Nat}
      (h : BorrowFields before cells parts loans) (hg : PartialGraphFields before cells parts reads)
      (hk : Retains before after reads) : BorrowFields after cells parts loans := by
    cases h with
    | nil => exact .nil
    | cons first rest => cases hg with
      | cons data tail =>
        exact .cons (first.transport data (hk.weaken (fun _ ha => List.mem_append_left _ ha)))
          (rest.transport tail (hk.weaken (fun _ ha => List.mem_append_right _ ha)))
end

theorem ResourceRep.transport {before after : Memory} {cell : Cell} {part : Slot} {r : Resources}
    (h : ResourceRep before cell part r) (hk : Retains before after r.reads) : ResourceRep after cell part r :=
  ⟨h.graph.transport hk, h.graph.owner_transport h.owned hk, h.borrowed.transport h.graph hk⟩

end SubtreeProofs.Rust.LookupSource.Partial.Addressed
