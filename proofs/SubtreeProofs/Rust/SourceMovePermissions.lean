module

public import SubtreeProofs.Rust.SourceStoreTotality
public import SubtreeProofs.Rust.SourceEvalAddressedCompleteness

/-! Actual successful source move routes traverse initialized owned projections.
Their checked root is the original local stack root or a currently owned Box.
Global ownership and separate caller roots reduce move guards to shared loans;
shared read aliases outside that selected root remain permitted. -/

@[expose] public section

namespace SubtreeProofs.Rust.LookupSource.Partial.Addressed

open Heap

theorem Rep.take_locate_root {memory : Memory} {cell : Cell} {part : Slot} {owners : List Nat}
    (h : Rep memory cell part owners) (path : List Projection) {value : Value} {after : Slot}
    (ht : part.take path = some (value, after)) (pointer : Pointer) {moved : Cell} {target : Pointer}
    (hl : locatePath memory cell pointer path = some (moved, target)) :
    target.root = pointer.root ∨ target.root ∈ owners := by
  induction path generalizing cell part owners value after pointer with
  | nil => cases hl; exact Or.inl rfl
  | cons projection rest ih =>
    cases projection with
    | deref => cases h with
      | empty _ | boolean _ | number _ | shared _ | node _ => simp only [Slot.take, reduceCtorEq] at ht
      | @owned address child part childOwners hr hc =>
        cases hp : part.take rest with
        | none => simp [Slot.take, hp] at ht
        | some pair =>
          rcases pair with ⟨result, remaining⟩
          have located : locatePath memory child ⟨address, []⟩ rest = some (moved, target) := by
            simpa only [locatePath, hr, bind, Option.bind] using hl
          rcases ih hc hp ⟨address, []⟩ located with root | owner
          · exact Or.inr (List.mem_append_right _ (by simpa using root))
          · exact Or.inr (List.mem_append_left _ owner)
    | field variant index => cases h with
      | empty _ | boolean _ | number _ | shared _ | owned _ _ => simp only [Slot.take, reduceCtorEq] at ht
      | @node kind tag cells parts owners fields =>
        simp only [Slot.take] at ht
        split at ht
        next variantValid =>
          cases hg : parts[index]? with
          | none => simp [hg] at ht
          | some selected =>
            obtain ⟨raw, own, leading, trailing, hc, hp, he, _⟩ := fields.focus index hg
            cases hs : selected.take rest with
            | none => simp [hg, hs] at ht
            | some pair =>
              rcases pair with ⟨result, remaining⟩
              have located : locatePath memory raw (pointer.field index) rest = some (moved, target) := by
                simpa only [locatePath, variantValid, ite_true, hc, bind, Option.bind] using hl
              rcases ih hp hs (pointer.field index) located with root | owner
              · exact Or.inl root
              · rw [he]
                exact Or.inr (List.mem_append_left _ (List.mem_append_right _ owner))
        next => cases ht

namespace Storage

theorem Activation.move_route {world : World} {active : Activation} (ha : active.Valid world)
    {place : Place} {value : Value} {after : Partial.Locals}
    (hm : active.state.move place = some (value, after)) {moved : Cell} {target : Pointer}
    (hl : locate world active.roots place = some (moved, target)) :
    ∃ slot binding, active.roots slot = some binding ∧
      (target.root = binding.address ∨ target.root ∈ active.owners world) := by
  have bound := Activation.move_root_lt ha hm
  rcases split : splitPlace place with ⟨slot, path⟩
  have index : slot < active.count := by simpa only [split] using bound
  obtain ⟨_, frame⟩ := ha.2
  simp only [Partial.Locals.move, split] at hm
  cases ht : (active.state slot).take path with
  | none => simp [ht] at hm
  | some pair =>
    rcases pair with ⟨value, part⟩
    cases hb : active.roots slot with
    | none =>
      have empty : active.state slot = .empty := by simpa only [hb] using frame.slots slot
      rw [empty, take_empty] at ht
      cases ht
    | some binding =>
      obtain ⟨root, _, hc, _, _, _⟩ := frame.get hb
      have owned : Rep world.memory root (active.state slot)
          (ownerState world.memory (rawAt world active.roots) active.state slot) := by
        have represented := frame.ownerState slot
        simp only [rawAt, hb, hc, bind, Option.bind] at represented
        exact represented.some_inv
      have located : locatePath world.memory root ⟨binding.address, []⟩ path = some (moved, target) := by
        simpa only [locate, split, hb, hc, bind, Option.bind] using hl
      refine ⟨slot, binding, hb, ?_⟩
      rcases owned.take_locate_root path ht ⟨binding.address, []⟩ located with root | owner
      · exact Or.inl root
      · apply Or.inr
        exact List.mem_flatMap.mpr ⟨slot, List.mem_range.mpr index, owner⟩

theorem Activation.move_not_in_caller_reads {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {suspended : Resources} (callerView : Callers world callers suspended)
    {place : Place} {value : Value} {after : Partial.Locals}
    (hm : active.state.move place = some (value, after)) {moved : Cell} {target : Pointer}
    (hl : locate world active.roots place = some (moved, target))
    (loans : target.root ∉ suspended.loans) : target.root ∉ suspended.reads := by
  have callerBoxes : BoxOwners world suspended.owners := by
    intro address member
    rw [← callerView.owners] at member
    exact hf.classified address (List.mem_append_right _ (List.mem_append_left _ member))
  obtain ⟨slot, binding, hb, route⟩ := Activation.move_route ha hm hl
  rcases route with stackRoot | owned
  · rw [stackRoot] at loans ⊢
    exact Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerBoxes loans
  · have classified := hf.classified target.root (List.mem_append_left _ owned)
    intro read
    rcases callerView.read_cases read with owner | borrowed | ⟨caller, hm, index, binding, hr, he⟩
    · have disjoint := hf.unique.disjoint
      rw [← callerView.owners] at owner
      exact List.disjoint_left.mp disjoint owned (List.mem_append_left _ owner)
    · exact loans borrowed
    · obtain ⟨_, current, _, _, _⟩ := callerView.get hm
      obtain ⟨_, _, _, stack, _, _⟩ := current.frame.get hr
      rw [he] at classified
      cases classified.symm.trans stack

end Storage
end SubtreeProofs.Rust.LookupSource.Partial.Addressed

namespace SubtreeProofs.Rust.SourceEval.Addressed

open LookupSource Heap Partial Partial.Addressed Storage

theorem allowed_local {world : World} {roots : Roots} {blocked : List Nat} {slot : Nat} {binding : Binding}
    (hb : roots slot = some binding) (clear : binding.address ∉ blocked) :
    Allowed world roots blocked (.move (.local slot)) := by
  intro moved target located
  cases hm : world.memory[binding.address]? with
  | none => simp [Storage.locate, splitPlace, hb, hm] at located
  | some cell =>
    simp only [Storage.locate, splitPlace, hb, hm, locatePath, bind, Option.bind, Option.some.injEq, Prod.mk.injEq] at located
    obtain ⟨rfl, rfl⟩ := located
    exact clear

theorem allowed_local_from_loans {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {current suspended : Resources} (callerView : Callers world callers suspended)
    {slot : Nat} {binding : Binding} (hb : active.roots slot = some binding)
    (loans : binding.address ∉ current.loans ++ suspended.loans) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move (.local slot)) := by
  have callerBoxes : BoxOwners world suspended.owners := by
    intro address member
    rw [← callerView.owners] at member
    exact hf.classified address (List.mem_append_right _ (List.mem_append_left _ member))
  apply allowed_local hb
  intro forbidden
  rcases List.mem_append.mp forbidden with own | caller
  · exact loans (List.mem_append_left _ own)
  · exact Activation.RootsSeparate.caller_root_not_read ha separate hb callerView callerBoxes
      (fun member => loans (List.mem_append_right _ member)) caller

theorem move_allowed_from_loans {world : World} {active : Activation} {callers : List Activation}
    (ha : active.Valid world) (separate : active.RootsSeparate callers) {external : List Nat}
    (hf : OwnerFrame world (active.owners world ++ (callerOwners world callers ++ external)))
    {current suspended : Resources} (callerView : Callers world callers suspended)
    {place : Place} {value : Value} {after : State}
    (hm : active.state.move place = some (value, after))
    (loans : ∀ moved target, locate world active.roots place = some (moved, target) →
      target.root ∉ current.loans ++ suspended.loans) :
    Allowed world active.roots (current.loans ++ suspended.reads) (.move place) := by
  intro moved target located forbidden
  have clear := loans moved target located
  rcases List.mem_append.mp forbidden with own | caller
  · exact clear (List.mem_append_left _ own)
  · exact Activation.move_not_in_caller_reads ha separate hf callerView hm located
      (fun member => clear (List.mem_append_right _ member)) caller

end SubtreeProofs.Rust.SourceEval.Addressed
