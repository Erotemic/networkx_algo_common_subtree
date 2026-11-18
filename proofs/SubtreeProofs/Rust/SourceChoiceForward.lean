module

public import SubtreeProofs.Rust.SourceClosedMachine
public import SubtreeProofs.Rust.SourceChoicePermissions
public import SubtreeProofs.Rust.SourceEvalCallingChoice

/-! Construct the actual pinned choice machine from independent native inputs.
The straight-line prelude allocates its real local roots, copies both scores,
and moves them into the comparison. No successful addressed run is a premise. -/

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def prelude : List Action :=
  [.storageLive 0, .storageLive 3, .storageLive 4,
   .assign 4 (.use (.copy (.field (.local 1) none 1))), .storageLive 5,
   .assign 5 (.use (.copy (.field (.local 2) none 1))),
   .assign 3 (.less (.move (.local 4)) (.move (.local 5)))]

theorem prelude_complete {before world : World} {active : Activation} {callers : List Activation}
    {previous : Resources} {external : List Nat}
    (h : ClosedMachine before callers previous external world active)
    (count : active.count = 6) (first second : CommonEmbedding)
    (state : active.state = initialState [encodeResult first, encodeResult second])
    (zero : active.roots 0 = none) (three : active.roots 3 = none)
    (four : active.roots 4 = none) (five : active.roots 5 = none) :
    ∃ final after, ClosedSteps callers world active prelude final after ∧
      ClosedMachine before callers previous external final after ∧
      after.count = 6 ∧ after.state = (initialState [encodeResult first, encodeResult second]).set 3
        (.boolean (decide (first.edges.val < second.edges.val))) ∧
      after.roots 1 = active.roots 1 ∧ after.roots 2 = active.roots 2 ∧
      (∃ binding, after.roots 0 = some binding) ∧ (∃ binding, after.roots 3 = some binding) ∧
      (∃ binding, after.roots 4 = some binding) ∧ (∃ binding, after.roots 5 = some binding) := by
  let w0 := world.allocate (.stack active.frame 0 world.memory.length) (.node .tuple 0 [])
  let a0 : Activation := {active with roots := active.roots.set 0 (some ⟨world.memory.length, world.memory.length⟩), state := active.state.set 0 .empty}
  obtain ⟨r0, h0⟩ := h.storageLive (slot := 0) (by omega) zero
  change ClosedMachine before callers previous external w0 a0 at h0
  let w3 := w0.allocate (.stack a0.frame 3 w0.memory.length) (.node .tuple 0 [])
  let a3 : Activation := {a0 with roots := a0.roots.set 3 (some ⟨w0.memory.length, w0.memory.length⟩), state := a0.state.set 3 .empty}
  obtain ⟨r3, h3⟩ := h0.storageLive (slot := 3) (by simp [a0, count]) (by simpa [a0, Roots.set] using three)
  change ClosedMachine before callers previous external w3 a3 at h3
  let w4 := w3.allocate (.stack a3.frame 4 w3.memory.length) (.node .tuple 0 [])
  let a4 : Activation := {a3 with roots := a3.roots.set 4 (some ⟨w3.memory.length, w3.memory.length⟩), state := a3.state.set 4 .empty}
  obtain ⟨r4, h4⟩ := h3.storageLive (slot := 4) (by simp [a3, a0, count])
    (by simpa [a3, a0, Roots.set] using four)
  change ClosedMachine before callers previous external w4 a4 at h4
  have firstWidth : first.edges.val < 2^32 := first.edges.hmax
  have secondWidth : second.edges.val < 2^32 := second.edges.hmax
  norm_num at firstWidth secondWidth
  obtain ⟨c4, rc4, hc4⟩ := h4.assign (slot := 4) (binding := ⟨w3.memory.length, w3.memory.length⟩)
    (by simp [a4, Roots.set])
    (rhs := .use (.copy (.field (.local 1) none 1))) (value := .number first.edges.val) (middle := a4.state)
    (by simp [a4, a3, a0, state, SourceEval.expression, SourceEval.operand, initialState, Partial.Locals.lift,
      initialEnv, Partial.Locals.set, Partial.Locals.read, splitPlace, Slot.read, Slot.get,
      encodeResult, Slot.ofValue, ofFields, Slot.materialize, firstWidth])
    (by simp [a4, Partial.Locals.set]) trivial h4.closed (.number firstWidth) .u32
  let wc4 := w4.write w3.memory.length c4
  let ac4 : Activation := {a4 with state := a4.state.set 4 (Slot.ofValue (.number first.edges.val))}
  change ClosedMachine before callers previous external wc4 ac4 at hc4
  let w5 := wc4.allocate (.stack ac4.frame 5 wc4.memory.length) (.node .tuple 0 [])
  let a5 : Activation := {ac4 with roots := ac4.roots.set 5 (some ⟨wc4.memory.length, wc4.memory.length⟩), state := ac4.state.set 5 .empty}
  obtain ⟨r5, h5⟩ := hc4.storageLive (slot := 5) (by simp [ac4, a4, a3, a0, count])
    (by simpa [ac4, a4, a3, a0, Roots.set] using five)
  change ClosedMachine before callers previous external w5 a5 at h5
  obtain ⟨c5, rc5, hc5⟩ := h5.assign (slot := 5) (binding := ⟨wc4.memory.length, wc4.memory.length⟩)
    (by simp [a5, Roots.set])
    (rhs := .use (.copy (.field (.local 2) none 1))) (value := .number second.edges.val) (middle := a5.state)
    (by simp [a5, ac4, a4, a3, a0, state, SourceEval.expression, SourceEval.operand, initialState, Partial.Locals.lift,
      initialEnv, Partial.Locals.set, Partial.Locals.read, splitPlace, Slot.read, Slot.get,
      encodeResult, Slot.ofValue, ofFields, Slot.materialize, secondWidth])
    (by simp [a5, Partial.Locals.set]) trivial h5.closed (.number secondWidth) .u32
  let wc5 := w5.write wc4.memory.length c5
  let ac5 : Activation := {a5 with state := a5.state.set 5 (Slot.ofValue (.number second.edges.val))}
  change ClosedMachine before callers previous external wc5 ac5 at hc5
  obtain ⟨c3, rc3, hc3⟩ := hc5.assign (slot := 3) (binding := ⟨w0.memory.length, w0.memory.length⟩)
    (by simp [ac5, a5, ac4, a4, a3, Roots.set])
    (rhs := .less (.move (.local 4)) (.move (.local 5)))
    (value := .boolean (decide (first.edges.val < second.edges.val))) (middle := (ac5.state.set 4 .empty).set 5 .empty)
    (by simp [ac5, a5, ac4, a4, a3, a0, state, SourceEval.expression, SourceEval.operand,
      Partial.Locals.move, Partial.Locals.set, splitPlace, Slot.take, Slot.ofValue, Slot.materialize,
      less32, firstWidth, secondWidth])
    (by simp [ac5, a5, ac4, a4, a3, Partial.Locals.set]) ⟨trivial, trivial⟩
    ((hc5.closed.clear 4).clear 5) (.boolean _) .boolean
  refine ⟨_, _, ClosedSteps.cons h.closed r0 (.cons h0.closed r3 (.cons h3.closed r4
    (.cons h4.closed rc4 (.cons hc4.closed r5 (.cons h5.closed rc5 (.cons hc5.closed rc3 (.nil _ _))))))),
    hc3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [ac5, a5, ac4, a4, a3, a0] using count
  · funext index
    by_cases h0 : index = 0
    · subst index; simp [ac5, a5, ac4, a4, a3, a0, initialState, Partial.Locals.lift, initialEnv, Partial.Locals.set]
    · by_cases h3 : index = 3
      · subst index; simp [Partial.Locals.set, Slot.ofValue]
      · by_cases h4 : index = 4
        · subst index; simp [initialState, Partial.Locals.lift, initialEnv, Partial.Locals.set]
        · by_cases h5 : index = 5
          · subst index; simp [initialState, Partial.Locals.lift, initialEnv, Partial.Locals.set]
          · simp [ac5, a5, ac4, a4, a3, a0, state, Partial.Locals.set, h0, h3, h4, h5]
  all_goals simp [ac5, a5, ac4, a4, a3, a0, Roots.set]

end SubtreeProofs.Rust.SourceEval.Choice
