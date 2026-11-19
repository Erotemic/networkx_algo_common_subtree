module

public import SubtreeProofs.Rust.SourcePairRightProgram
public import SubtreeProofs.Rust.SourceOriginalOptionalPayload

/-! The pinned successful-right continuation as its actual finite action list.
Definitional equality connects this list and every selected suffix to finish;
no alternative algorithm, parser or interpreter is introduced. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource Heap Partial Partial.Addressed Storage SourceEval.Addressed verified_ordered_core

def finishActions : List Action :=
  [
    Action.storageLive 96,
    Action.assign 96 (Expr.use (Operand.move (Place.field (Place.local 88) (some 1) 0))),
    Action.assign 95 (Expr.use (Operand.move (Place.local 96))),
    Action.drop 96,
    Action.storageDead 96,
    Action.fakeRead (Place.local 95),
    Action.storageLive 99,
    Action.storageLive 100,
    Action.storageLive 101,
    Action.assign 101 (Expr.use (Operand.move (Place.local 64))),
    Action.storageLive 102,
    Action.assign 102 (Expr.use (Operand.move (Place.local 81))),
    Action.call (Function.chooseLonger) [Operand.move (Place.local 101), Operand.move (Place.local 102)] 100,
    Action.storageDead 102,
    Action.storageDead 101,
    Action.storageLive 103,
    Action.assign 103 (Expr.use (Operand.move (Place.local 95))),
    Action.call (Function.chooseLonger) [Operand.move (Place.local 100), Operand.move (Place.local 103)] 99,
    Action.storageDead 103,
    Action.storageDead 100,
    Action.fakeRead (Place.local 99),
    Action.storageLive 104,
    Action.storageLive 105,
    Action.assign 105 (Expr.use (Operand.move (Place.local 89))),
    Action.storageLive 106,
    Action.assign 106 (Expr.address (Place.deref (Place.local 1))),
    Action.storageLive 107,
    Action.assign 107 (Expr.address (Place.deref (Place.local 2))),
    Action.storageLive 108,
    Action.storageLive 109,
    Action.assign 109 (Expr.address (Place.local 99)),
    Action.assign 108 (Expr.address (Place.deref (Place.local 109))),
    Action.call (Function.insert) [Operand.move (Place.local 105), Operand.move (Place.local 106), Operand.move (Place.local 107), Operand.move (Place.local 108)] 104,
    Action.storageDead 108,
    Action.storageDead 107,
    Action.storageDead 106,
    Action.storageDead 105,
    Action.fakeRead (Place.local 104),
    Action.storageDead 109,
    Action.storageLive 110,
    Action.storageLive 111,
    Action.assign 111 (Expr.use (Operand.move (Place.local 99))),
    Action.assign 110 (Expr.aggregate (Kind.optional) 1 [Operand.move (Place.local 111)]),
    Action.drop 111,
    Action.storageDead 111,
    Action.storageLive 112,
    Action.assign 112 (Expr.use (Operand.move (Place.local 104))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 110), Operand.move (Place.local 112)]),
    Action.drop 112,
    Action.storageDead 112,
    Action.drop 110,
    Action.storageDead 110,
    Action.drop 104,
    Action.storageDead 104,
    Action.drop 99,
    Action.storageDead 99,
    Action.drop 95,
    Action.storageDead 95,
    Action.drop 89,
    Action.storageDead 89,
    Action.drop 88,
    Action.storageDead 88,
    Action.drop 85,
    Action.storageDead 85,
    Action.drop 81,
    Action.storageDead 81,
    Action.drop 75,
    Action.storageDead 75,
    Action.drop 74,
    Action.storageDead 74,
    Action.drop 71,
    Action.storageDead 71,
    Action.drop 64,
    Action.storageDead 64,
    Action.storageDead 58,
    Action.storageDead 51,
    Action.drop 47,
    Action.storageDead 47,
    Action.drop 42,
    Action.storageDead 42,
    Action.drop 41,
    Action.storageDead 41,
    Action.drop 37,
    Action.storageDead 37,
    Action.drop 32,
    Action.storageDead 32,
    Action.drop 31,
    Action.storageDead 31,
    Action.storageDead 30,
    Action.storageDead 29,
    Action.storageDead 28,
    Action.storageDead 27,
    Action.storageDead 13,
    Action.drop 3,
    Action.storageDead 3,
    Action.storageDead 2,
    Action.storageDead 1]

def finishCode (index : Nat) : Code := (finishActions.drop index).foldr Control.Tree.step .ret

theorem finish_actions : finish = finishActions.foldr Control.Tree.step .ret := rfl

theorem finish_payload_actions : finishActions.take 6 = optionalPayloadActions 88 96 95 := rfl

end SubtreeProofs.Rust.SourceEval.Evaluator
