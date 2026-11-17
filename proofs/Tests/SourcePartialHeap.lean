import SubtreeProofs.Rust.SourceEvalHeapMoveDrop

namespace SourcePartialHeapTests

open SubtreeProofs.Rust SubtreeProofs.Rust.LookupSource Heap Partial Partial.Addressed

private def e : Value := .node .word 0 []
private def headValue : Value := .node .word 1 [.boxed e, .boxed e]
private def wholeValue : Value := .node .word 1 [.boxed headValue, .boxed e]
private def headCell : Cell := .node .word 1 [.owned 0, .owned 1]
private def root : Cell := .node .word 1 [.owned 2, .owned 3]
private def memory : Memory := [.node .word 0 [], .node .word 0 [], headCell, .node .word 0 [], .number 99]
private def whole : Slot := Slot.ofValue wholeValue
private def remaining : Slot := .node .word 1 [.boxed .empty, .boxed (Slot.ofValue e)]
private def path : List Projection := [.field (some 1) 0, .deref]
private def place : Place := .deref (.field (.local 0) (some 1) 0)

private theorem head_rep : Represents memory headCell headValue :=
  .node (.cons (.owned (by rfl) (.node .nil)) (.cons (.owned (by rfl) (.node .nil)) .nil))
private theorem whole_rep : Represents memory root wholeValue :=
  .node (.cons (.owned (by rfl) head_rep) (.cons (.owned (by rfl) (.node .nil)) .nil))
private theorem whole_footprint : Footprint memory root [0, 1, 2, 3] :=
  .node (.cons (.owned (by rfl) (.node (.cons (.owned (by rfl) (.node .nil))
    (.cons (.owned (by rfl) (.node .nil)) .nil)))) (.cons (.owned (by rfl) (.node .nil)) .nil))
private theorem whole_partial : Rep memory root whole [0, 1, 2, 3] := Rep.of_full whole_rep whole_footprint
private theorem empty_box (address : Nat) (hr : memory[address]? = some (.node .word 0 [])) :
    Rep memory (.owned address) (.boxed (Slot.ofValue e)) [address] :=
  .owned hr (Rep.of_full (value := e) (.node .nil) (.node .nil))
private theorem remaining_partial : Rep memory root remaining [2, 3] := by
  apply Rep.node
  exact .cons (.owned (by rfl) (.empty headCell))
    (.cons (empty_box 3 (by rfl)) .nil)
private theorem frame_partial : Rep memory (.owned 4) (.boxed (.number 99)) [4] :=
  .owned (by rfl) (.number 99)
private theorem take_head : whole.take path = some (headValue, remaining) := by
  simp [whole, wholeValue, headValue, e, remaining, path, Slot.ofValue, ofFields,
    Slot.take, Slot.materialize, materializeFields]

-- Payload owners transfer; the Box containing that payload remains owned by
-- the partial parent. The stored pointer identities remain unchanged.
example : ownedProjection memory root path = some headCell := rfl
example : destroy memory root remaining = some ([2, 3], ⟨4, 2⟩) := by decide +kernel
example : destroy memory (.owned 2) (.boxed .empty) = some ([2], ⟨1, 1⟩) := by decide +kernel
example : destroy memory root whole = some ([0, 1, 2, 3], ⟨9, 4⟩) := by decide +kernel
example : remaining.take path = none := by decide +kernel
example : remaining.materialize = none := by decide +kernel

private theorem separated : Separated memory [root, .owned 4] [whole, .boxed (.number 99)] :=
  ⟨[0, 1, 2, 3, 4], .cons whole_partial (.cons frame_partial .nil), by decide +kernel⟩
example : ∃ moved, ownedProjection memory root path = some moved ∧ Represents memory moved headValue ∧
    Separated memory [moved, root, .owned 4] [Slot.ofValue headValue, remaining, .boxed (.number 99)] :=
  separated.take path take_head

-- Typed readback reuses the independent heap type and field signatures.
private theorem whole_typed : SlotTyped whole (.adt .word) :=
  ofValue_typed (.node .pairWord (.cons (.owned (.node .pairWord
    (.cons (.owned (.node .emptyWord .nil)) (.cons (.owned (.node .emptyWord .nil)) .nil))))
    (.cons (.owned (.node .emptyWord .nil)) .nil)))
example : ∃ moved a b, ownedProjection memory root path = some moved ∧ Typed memory moved (.adt .word) ∧
    Footprint memory moved a ∧ Rep memory root remaining b ∧ SlotTyped remaining (.adt .word) ∧
    ([0, 1, 2, 3] : List Nat).Perm (a ++ b) :=
  whole_partial.take_typed whole_typed path
    (by simp [path, inferPath, SourceTypes.fieldType, SourceTypes.constructorFields, SourceTypes.deref]) take_head

-- Fresh Box creation adds one concrete owner while retaining the caller frame.
example : Separated (Heap.alloc memory root).2 [(Heap.alloc memory root).1, .owned 4]
    [.boxed whole, .boxed (.number 99)] := separated.alloc
example (body : SourceEval.Function → SourceEval.Code) (fuel : Nat) :
    SourceEval.run body (fuel + 1) .boxNew [wholeValue] =
        some (.boxed wholeValue, SourceEval.Cost.entry .boxNew) ∧
      Rep (Heap.alloc memory root).2 (Heap.alloc memory root).1 (Slot.ofValue (.boxed wholeValue))
        ([0, 1, 2, 3] ++ [memory.length]) ∧
      Extends memory (Heap.alloc memory root).2 ∧ memory[memory.length]? = none ∧
      (Heap.alloc memory root).2.length = memory.length + 1 :=
  SourceEval.AddressedPrimitives.box_new body fuel whole_partial

-- Source drop consumes the actual partial local, charges each visit once and
-- retires precisely its two remaining owners while protecting moved/frame data.
private def raw : Heap.Locals := fun index => if index = 0 then some root else if index = 1 then some (.owned 4) else none
private def state : Partial.Locals := fun index => if index = 0 then whole else if index = 1 then .boxed (.number 99) else .empty
private def owners : OwnerState := fun index => if index = 0 then [0, 1, 2, 3] else if index = 1 then [4] else []
private def live : Live := fun address => decide (address < memory.length)
private def after : Partial.Locals := state.set 0 remaining
private def afterOwners : OwnerState := owners.set 0 [2, 3]
private def calls : SourceEval.Calls := fun _ _ => none
private theorem env_rep : Partial.Addressed.EnvRep memory raw state owners := by
  intro index
  by_cases hz : index = 0
  · subst index
    exact .stored whole_partial
  · by_cases ho : index = 1
    · subst index
      exact .stored frame_partial
    · simp only [raw, state, owners, hz, ho, ite_false]
      exact .empty
private theorem after_rep : Partial.Addressed.EnvRep memory raw after afterOwners :=
  env_rep.remask (slot := 0) (cell := root) rfl remaining_partial
private theorem source_move : SourceEval.operand state (.move place) = some (headValue, after) := by
  change (do let (value, part) ← whole.take path; some (value, state.set 0 part)) = some (headValue, after)
  rw [take_head]
  rfl

example : ∃ sourceRoot moved a b,
    raw 0 = some sourceRoot ∧ ownedProjection memory sourceRoot path = some moved ∧
    Represents memory moved headValue ∧ Footprint memory moved a ∧
    Partial.Addressed.EnvRep memory raw after (owners.set 0 b) ∧ (owners 0).Perm (a ++ b) :=
  SourceEval.AddressedPrimitives.operand_move env_rep source_move

example : ∃ cost,
    SourceEval.action calls after (.drop 0) = some (after.set 0 .empty, cost) ∧
    destroyLocal memory (raw 0) (after 0) = some ([2, 3], cost.destroyed) ∧
    cost.work.steps = 5 ∧ cost.destroyed.boxes = 2 ∧ AliveOn (retire live [2, 3]) [0, 1, 4] := by
  have hd := SourceEval.AddressedPrimitives.action_drop_retire after_rep calls 0
    (live := live) (guarded := [0, 1, 4])
    (by simp [AliveOn, afterOwners, OwnerState.set, live, memory])
    (by decide +kernel) (by simp [afterOwners, OwnerState.set])
    (by simp [AliveOn, live, memory])
  exact ⟨SourceEval.Cost.local 1 (after 0).dropWork, hd.2.1, hd.1,
    by decide +kernel, by decide +kernel, hd.2.2.2.2.2.2⟩

example : ¬ AliveOn (retire live [2, 3]) [2, 3] := retired_not_alive live (by decide +kernel)
example : destroy memory (.shared ⟨2, []⟩) (.shared headValue) = some ([], ⟨1, 0⟩) := by decide +kernel
example : ownedProjection memory (.shared ⟨2, []⟩) [.deref] = none := rfl

-- Duplicate ownership is a separate invariant from data representation.
private def aliasCell : Cell := .node .tuple 0 [.owned 0, .owned 0]
private def aliasMask : Slot := .node .tuple 0 [.boxed (Slot.ofValue e), .boxed (Slot.ofValue e)]
private theorem alias_rep : Rep memory aliasCell aliasMask [0, 0] := by
  apply Rep.node
  exact .cons (empty_box 0 (by rfl)) (.cons (empty_box 0 (by rfl)) .nil)
example : ¬ Separated memory [aliasCell] [aliasMask] := by
  rintro ⟨list, hr, hn⟩
  cases hr with
  | cons first rest =>
    cases rest
    have he := first.unique alias_rep
    simp [he] at hn

-- Shared aliases own no addresses. Owner separation alone can therefore hold
-- while retirement invalidates a shared target; the guarded-address premise
-- must be supplied by the future dynamic loan interpretation.
example : Separated memory [root, .shared ⟨2, []⟩] [remaining, .shared headValue] :=
  ⟨[2, 3], .cons remaining_partial (.cons (.shared (.shared (by rfl) head_rep)) .nil), by decide +kernel⟩
example : retire live [2, 3] 2 = false := by decide +kernel
example : ¬ (∀ address ∈ ([2] : List Nat), address ∉ ([2, 3] : List Nat)) := by simp

-- Existing native packing/ownership intervals are reused for all finite words.
example (word : verified_ordered_core.BalancedWord) (prior : Memory) :
    destroy (packWord word prior).2 (packWord word prior).1 (Slot.ofValue (encodeWord word)) =
      some (List.range' prior.length ((packWord word prior).2.length - prior.length),
        (Slot.ofValue (encodeWord word)).dropWork) := destroy_packed_word word prior

end SourcePartialHeapTests
