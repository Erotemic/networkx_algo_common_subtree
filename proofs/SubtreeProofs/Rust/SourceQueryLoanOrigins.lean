module

public import SubtreeProofs.Rust.SourceCallingPrefixes

/-! Query loan origins are actual local inventories with a bound on their
borrowed addresses. They allow shared queries to intersect owned table data;
only later selected stack-root permissions use the bound. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

open Heap

theorem LocalResources.unique {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals}
    {first second : Resources} (h : LocalResources world frame roots state slot first)
    (other : LocalResources world frame roots state slot second) : first = second :=
  Option.some.inj (h.inspect.symm.trans other.inspect)

theorem LocalResources.congr_at {world : World} {frame slot : Nat} {roots nextRoots : Roots}
    {state nextState : Partial.Locals} {r : Resources} (h : LocalResources world frame roots state slot r)
    (root : nextRoots slot = roots slot) (mask : nextState slot = state slot) :
    LocalResources world frame nextRoots nextState slot r := by
  cases h with
  | vacant emptyRoot emptyMask => exact .vacant (root.trans emptyRoot) (mask.trans emptyMask)
  | stored hb memory classified represented alive =>
    exact .stored (root.trans hb) memory classified (mask ▸ represented) alive

theorem LocalResources.clear {world : World} {frame slot : Nat} {roots : Roots} {state : Partial.Locals}
    {r : Resources} (h : LocalResources world frame roots state slot r) :
    ∃ after, LocalResources world frame roots (state.set slot .empty) slot after ∧ after.loans = [] := by
  cases h with
  | vacant root _ => exact ⟨{}, .vacant root (by simp only [Partial.Locals.set, ite_true]), rfl⟩
  | @stored binding cell data root memory classified represented alive =>
    refine ⟨({} : Resources).atRoot binding.address,
      .stored root memory classified ?_ ?_, rfl⟩
    · simpa only [Partial.Locals.set, ite_true] using
        (show ResourceRep world.memory cell .empty {} from ⟨.empty cell, .empty cell, .empty cell⟩)
    · intro address member
      exact alive address (List.mem_append_right _ member)

theorem LocalResources.reads_avoid_fresh_root {world : World} {active : Activation} {index slot : Nat}
    {r : Resources} (h : LocalResources world active.frame active.roots active.state index r)
    (valid : active.Valid world) {binding : Binding} (hb : active.roots slot = some binding)
    (different : index ≠ slot) (zero : (active.state index).dropWork.boxes = 0) {limit : Nat}
    (bound : ∀ address ∈ r.loans, address < limit) (fresh : limit ≤ binding.address) : binding.address ∉ r.reads := by
  intro forbidden
  rcases h.read_cases forbidden with owned | borrowed | ⟨target, ht, same⟩
  · have none : r.owners = [] := List.length_eq_zero_iff.mp (h.boxes.trans zero)
    rw [none] at owned
    cases owned
  · have old := bound binding.address borrowed
    omega
  · obtain ⟨_, frame⟩ := valid.2
    exact different (frame.distinct ht hb same.symm)

end SubtreeProofs.Rust.LookupSource.Partial.Addressed.Storage

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

def ClosedOutside (exceptions : List Nat) (state : State) : Prop :=
  ∀ slot, slot ∉ exceptions → ∃ ty, SlotTyped (state slot) ty ∧ Borrow.Closed ty

theorem ClosedOutside.set {exceptions : List Nat} {state : State} (h : ClosedOutside exceptions state)
    (slot : Nat) {part : Slot} {ty : Ty} (typed : SlotTyped part ty) (closed : Borrow.Closed ty) :
    ClosedOutside exceptions (state.set slot part) := by
  intro index outside
  by_cases same : index = slot
  · subst index; exact ⟨ty, by simpa only [Partial.Locals.set, ite_true] using typed, closed⟩
  · simpa only [Partial.Locals.set, same, ite_false] using h index outside

theorem ClosedOutside.clear {exceptions : List Nat} {state : State} (h : ClosedOutside exceptions state) (slot : Nat) :
    ClosedOutside exceptions (state.set slot .empty) := h.set slot (.empty .u32) .u32

theorem ClosedOutside.forget {exceptions : List Nat} {state : State} (h : ClosedOutside exceptions state)
    (code : Code) (slots : List Nat) : ClosedOutside exceptions (LoanEnding.forget code slots state) := by
  intro index outside
  rcases LoanEnding.forget_eq_or_empty code slots state index with same | empty
  · simpa only [same] using h index outside
  · exact ⟨.u32, by rw [empty]; exact .empty _, .u32⟩

def LoanOrigin (world : World) (active : Activation) (limit slot : Nat) : Prop :=
  ∃ r, LocalResources world active.frame active.roots active.state slot r ∧ ∀ address ∈ r.loans, address < limit

theorem LoanOrigin.bound {world : World} {active : Activation} {limit slot : Nat}
    (h : LoanOrigin world active limit slot) {r : Resources}
    (represented : LocalResources world active.frame active.roots active.state slot r) :
    ∀ address ∈ r.loans, address < limit := by
  obtain ⟨initial, old, bound⟩ := h
  rw [← old.unique represented]
  exact bound

theorem LoanOrigin.of_closed {world : World} {active : Activation} (ha : active.Valid world)
    (limit slot : Nat) {ty : Ty} (typed : SlotTyped (active.state slot) ty) (closed : Borrow.Closed ty) :
    LoanOrigin world active limit slot := by
  obtain ⟨_, frame⟩ := ha.2
  obtain ⟨r, _, represented⟩ := frame.inspectSlot slot
  refine ⟨r, represented, ?_⟩
  rw [represented.closed_loans typed closed]
  simp

theorem LoanOrigin.congr {world : World} {active after : Activation} {limit slot : Nat}
    (h : LoanOrigin world active limit slot) (frame : after.frame = active.frame)
    (root : after.roots slot = active.roots slot) (mask : after.state slot = active.state slot) :
    LoanOrigin world after limit slot := by
  obtain ⟨r, represented, bound⟩ := h
  refine ⟨r, ?_, bound⟩
  rw [frame]
  exact represented.congr_at root mask

theorem LoanOrigin.transport {before after : World} {active : Activation} {limit slot : Nat}
    (h : LoanOrigin before active limit slot)
    (kept : ∀ r, LocalResources before active.frame active.roots active.state slot r → Preserves before after r.reads) :
    LoanOrigin after active limit slot := by
  obtain ⟨r, represented, bound⟩ := h
  exact ⟨r, represented.transport (kept r represented), bound⟩

theorem LoanOrigin.prepare {world : World} {active : Activation} {limit slot : Nat}
    (h : LoanOrigin world active limit slot) (code : Code) : LoanOrigin world (active.forgetRefs code) limit slot := by
  obtain ⟨r, represented, bound⟩ := h
  rcases LoanEnding.forget_eq_or_empty code (List.range active.count) active.state slot with same | empty
  · exact ⟨r, represented.congr_at rfl same, bound⟩
  · obtain ⟨after, cleared, noLoans⟩ := represented.clear
    refine ⟨after, cleared.congr_at rfl ?_, ?_⟩
    · change LoanEnding.forget code (List.range active.count) active.state slot = (active.state.set slot .empty) slot
      simpa only [Partial.Locals.set, ite_true] using empty
    · rw [noLoans]; simp

theorem LoanOrigin.write_other {world : World} {active : Activation} {limit index slot : Nat}
    (h : LoanOrigin world active limit index) (valid : active.Valid world)
    {binding : Binding} (hb : active.roots slot = some binding) (different : index ≠ slot)
    (zero : (active.state index).dropWork.boxes = 0) (fresh : limit ≤ binding.address) (cell : Cell) :
    LoanOrigin (world.write binding.address cell) active limit index := by
  obtain ⟨r, represented, bound⟩ := h
  have clear := represented.reads_avoid_fresh_root valid hb different zero bound fresh
  exact ⟨r, represented.transport (world.write_preserves clear cell), bound⟩

theorem LoanOrigin.retire_other {world : World} {active : Activation} {limit index slot : Nat}
    (h : LoanOrigin world active limit index) (valid : active.Valid world)
    {binding : Binding} (hb : active.roots slot = some binding) (different : index ≠ slot)
    (zero : (active.state index).dropWork.boxes = 0) (fresh : limit ≤ binding.address) :
    LoanOrigin (world.retire [binding.address]) active limit index := by
  obtain ⟨r, represented, bound⟩ := h
  have clear := represented.reads_avoid_fresh_root valid hb different zero bound fresh
  have kept : Keeps world (world.retire [binding.address]) r.reads := world.retire_keeps (by
    intro address member removed
    have same := List.mem_singleton.mp removed
    subst address
    exact clear member)
  exact ⟨r, represented.transport kept.preserves, bound⟩

theorem LoanOrigin.allocate {world : World} {active : Activation} {limit index : Nat}
    (h : LoanOrigin world active limit index) (hw : world.WellFormed) (kind : Class) (cell : Cell) :
    LoanOrigin (world.allocate kind cell) active limit index := by
  obtain ⟨r, represented, bound⟩ := h
  exact ⟨r, represented.transport (world.allocate_keeps hw kind cell r.reads).preserves, bound⟩

def QueryOrigins (world : World) (active : Activation) (limit : Nat) : Prop :=
  ∀ slot ∈ [1, 2], LoanOrigin world active limit slot

theorem LoanOrigin.clear {world : World} {active : Activation} {limit slot : Nat}
    (h : LoanOrigin world active limit slot) : LoanOrigin world {active with state := active.state.set slot .empty} limit slot := by
  obtain ⟨r, represented, _⟩ := h
  obtain ⟨after, cleared, noLoans⟩ := represented.clear
  refine ⟨after, cleared, ?_⟩
  rw [noLoans]
  simp

theorem QueryOrigins.prepare {world : World} {active : Activation} {limit : Nat}
    (h : QueryOrigins world active limit) (code : Code) : QueryOrigins world (active.forgetRefs code) limit :=
  fun slot member => (h slot member).prepare code

def ReferenceQueries (state : State) : Prop :=
  ∀ slot ∈ [1, 2], state slot = .empty ∨ ∃ value, state slot = .shared value

theorem ReferenceQueries.boxes {state : State} (h : ReferenceQueries state) {slot : Nat} (member : slot ∈ [1, 2]) :
    (state slot).dropWork.boxes = 0 := by
  rcases h slot member with empty | ⟨value, shared⟩
  · rw [empty]; simp only [Slot.dropWork]
  · rw [shared]; simp only [Slot.dropWork]

theorem ReferenceQueries.clear {state : State} (h : ReferenceQueries state) (slot : Nat) :
    ReferenceQueries (state.set slot .empty) := by
  intro index member
  by_cases same : index = slot
  · subst index; exact Or.inl (by simp only [Partial.Locals.set, ite_true])
  · simpa only [Partial.Locals.set, same, ite_false] using h index member

theorem ReferenceQueries.prepare {state : State} (h : ReferenceQueries state) (code : Code) (slots : List Nat) :
    ReferenceQueries (LoanEnding.forget code slots state) := by
  intro index member
  rcases LoanEnding.forget_eq_or_empty code slots state index with same | empty
  · simpa only [same] using h index member
  · exact Or.inl empty

theorem QueryOrigins.congr {world : World} {active after : Activation} {limit : Nat}
    (h : QueryOrigins world active limit) (frame : after.frame = active.frame)
    (roots : ∀ slot ∈ [1, 2], after.roots slot = active.roots slot)
    (masks : ∀ slot ∈ [1, 2], after.state slot = active.state slot) : QueryOrigins world after limit :=
  fun slot member => (h slot member).congr frame (roots slot member) (masks slot member)

theorem QueryOrigins.set_other {world : World} {active : Activation} {limit : Nat}
    (h : QueryOrigins world active limit) (slot : Nat) (different : slot ∉ [1, 2]) (part : Slot) :
    QueryOrigins world {active with state := active.state.set slot part} limit := by
  apply h.congr (after := {active with state := active.state.set slot part}) rfl (fun _ _ => rfl)
  intro index member
  have other : index ≠ slot := by intro same; subst index; exact different member
  simp only [Partial.Locals.set, other, ite_false]

theorem ReferenceQueries.set_other {state : State} (h : ReferenceQueries state)
    (slot : Nat) (different : slot ∉ [1, 2]) (part : Slot) : ReferenceQueries (state.set slot part) := by
  intro index member
  have other : index ≠ slot := by intro same; subst index; exact different member
  simpa only [Partial.Locals.set, other, ite_false] using h index member

theorem QueryOrigins.clear {world : World} {active : Activation} {limit : Nat}
    (h : QueryOrigins world active limit) (slot : Nat) : QueryOrigins world {active with state := active.state.set slot .empty} limit := by
  intro index member
  by_cases same : index = slot
  · subst index; exact (h slot member).clear
  · exact (h index member).congr (after := {active with state := active.state.set slot .empty}) rfl rfl
      (by simp only [Partial.Locals.set, same, ite_false])

theorem QueryOrigins.allocate {world : World} {active : Activation} {limit : Nat}
    (h : QueryOrigins world active limit) (hw : world.WellFormed) (slot : Nat) (different : slot ∉ [1, 2]) :
    let final := world.allocate (.stack active.frame slot world.memory.length) (.node .tuple 0 [])
    let after : Activation := {active with roots := active.roots.set slot (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set slot .empty}
    QueryOrigins final after limit := by
  dsimp only
  intro index member
  have other : index ≠ slot := by intro same; subst index; exact different member
  exact ((h index member).allocate hw _ _).congr rfl
    (by simp only [Roots.set, other, ite_false]) (by simp only [Partial.Locals.set, other, ite_false])

theorem QueryOrigins.write_other {world : World} {active : Activation} {limit slot : Nat}
    (h : QueryOrigins world active limit) (valid : active.Valid world) (refs : ReferenceQueries active.state)
    {binding : Binding} (hb : active.roots slot = some binding) (different : slot ∉ [1, 2])
    (fresh : limit ≤ binding.address) (cell : Cell) : QueryOrigins (world.write binding.address cell) active limit := by
  intro index member
  have other : index ≠ slot := by intro same; subst index; exact different member
  exact (h index member).write_other valid hb other (refs.boxes member) fresh cell

theorem QueryOrigins.retire_other {world : World} {active : Activation} {limit slot : Nat}
    (h : QueryOrigins world active limit) (valid : active.Valid world) (refs : ReferenceQueries active.state)
    {binding : Binding} (hb : active.roots slot = some binding) (different : slot ∉ [1, 2])
    (fresh : limit ≤ binding.address) :
    let after : Activation := {active with roots := active.roots.set slot none, state := active.state.set slot .empty}
    QueryOrigins (world.retire [binding.address]) after limit := by
  dsimp only
  intro index member
  have other : index ≠ slot := by intro same; subst index; exact different member
  exact ((h index member).retire_other valid hb other (refs.boxes member) fresh).congr rfl
    (by simp only [Roots.set, other, ite_false]) (by simp only [Partial.Locals.set, other, ite_false])

theorem Inventory.loans_below_queries {world : World} {active : Activation} {limit : Nat}
    {slots : List Nat} {r : Resources}
    (h : Inventory world active.frame active.roots active.state slots r)
    (closed : ClosedOutside [1, 2] active.state) (queries : QueryOrigins world active limit) :
    ∀ address ∈ r.loans, address < limit := by
  induction h with
  | nil => simp
  | @cons slot slots head tail represented rest ih =>
    have headBound : ∀ address ∈ head.loans, address < limit := by
      by_cases member : slot ∈ [1, 2]
      · exact (queries slot member).bound represented
      · obtain ⟨ty, typed, shape⟩ := closed slot member
        rw [represented.closed_loans typed shape]
        simp
    intro address member
    rcases List.mem_append.mp member with first | remaining
    · exact headBound address first
    · exact ih address remaining

end SubtreeProofs.Rust.SourceEval.Addressed
