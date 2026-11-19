module

public import SubtreeProofs.Rust.SourceEvalLegacyRun
public import SubtreeProofs.Rust.OrderedSolver
public import SubtreeProofs.Rust.SourceEvalChoiceProgram

/-! The owned score-choice body, with explicit move and losing-value drop.
The independent native tie rule is reused; its actual source identity is checked
separately in SourceEvalChoiceCertificate. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Choice

open LookupSource LookupSource.Partial verified_ordered_core

def loser (first second : CommonEmbedding) : CommonEmbedding :=
  if first.edges < second.edges then first else second

def destroyed (first second : CommonEmbedding) : DropWork :=
  (Slot.ofValue (encodeResult (loser first second))).dropWork

def cost (first second : CommonEmbedding) : Cost :=
  ⟨⟨27 + (destroyed first second).visits, {}⟩, destroyed first second, 0⟩

theorem body_exec (call : Calls) (first second : CommonEmbedding) :
    exec call body (initialState [encodeResult first, encodeResult second]) =
      some (.returned (encodeResult (OrderedSolver.selectResult first second)),
        ⟨⟨26 + (destroyed first second).visits, {}⟩, destroyed first second, 0⟩) := by
  have hf : first.edges.val < 2^32 := first.edges.hmax
  have hs : second.edges.val < 2^32 := second.edges.hmax
  norm_num at hf hs
  by_cases hc : first.edges.val < second.edges.val <;>
    simp [body, branch, exec, Control.execWith, action, expression, operand,
      scrutinee, returnValue, nextState, Control.selectSource, Control.selectIndex,
      initialState, Locals.lift, initialEnv, Locals.set, Locals.move, Locals.drop, Locals.read,
      splitPlace, Slot.take, Slot.get, Slot.read, Slot.materialize_ofValue,
      encodeResult, Slot.ofValue, Slot.materialize, materializeFields, ofFields,
      hf, hs, hc, destroyed, loser, OrderedSolver.selectResult, Slot.dropWork, dropFields,
      less32, Cost.local, Cost.plus, LookupSource.Cost.plus, LookupEvents.Events.plus, DropWork.plus,
      Action.weight, Expr.weight, Operand.weight, Place.weight, LookupSource.Scrutinee.weight,
      LookupSource.Operand.weight, bind, Option.bind, pure, Option.map] <;> omega

theorem word_dropWork (word : BalancedWord) :
    (Slot.ofValue (encodeWord word)).dropWork =
      ⟨4 * (OrderedSolver.toDyck word).semilength + 1, 2 * (OrderedSolver.toDyck word).semilength⟩ := by
  induction word with
  | Empty => simp [encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus, OrderedSolver.toDyck]
  | Pair head tail ihHead ihTail =>
    simp only [encodeWord, Slot.ofValue, ofFields, Slot.dropWork, dropFields, DropWork.plus,
      ihHead, ihTail, OrderedSolver.toDyck, DyckWord.semilength_add, DyckWord.semilength_nest,
      DropWork.mk.injEq]
    constructor <;> omega

theorem result_dropWork (result : CommonEmbedding) :
    (Slot.ofValue (encodeResult result)).dropWork =
      ⟨4 * (OrderedSolver.toDyck result.word).semilength + 3, 2 * (OrderedSolver.toDyck result.word).semilength⟩ := by
  simp [encodeResult, Slot.ofValue, ofFields, Slot.dropWork, dropFields, word_dropWork, DropWork.plus]
  omega

theorem run_body (program : SourceEval.Function → Code) (hbody : program .chooseLonger = body)
    (fuel : Nat) (first second : CommonEmbedding) :
    run program (fuel + 1) .chooseLonger [encodeResult first, encodeResult second] =
      some (encodeResult (OrderedSolver.selectResult first second), cost first second) := by
  rw [Legacy.run_ordinary program fuel .chooseLonger _ (by decide) (by decide), hbody, body_exec]
  simp [bind, Option.bind, Cost.entry, entryEvents, Cost.plus, LookupSource.Cost.plus,
    LookupEvents.Events.plus, DropWork.plus, cost]
  omega

theorem cost_exact (first second : CommonEmbedding) :
    (cost first second).work.steps = 30 + 4 * (OrderedSolver.toDyck (loser first second).word).semilength ∧
    (cost first second).work.events = {} ∧
    (cost first second).destroyed.visits = 4 * (OrderedSolver.toDyck (loser first second).word).semilength + 3 ∧
    (cost first second).destroyed.boxes = 2 * (OrderedSolver.toDyck (loser first second).word).semilength ∧
    (cost first second).solverCalls = 0 := by
  simp only [cost, destroyed, result_dropWork, and_true]
  omega

end SubtreeProofs.Rust.SourceEval.Choice
