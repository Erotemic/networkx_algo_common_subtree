module

public import SubtreeProofs.Rust.SourceEvalMachine

/-! Reviewable control for the complete memo evaluator. Straight-line source
segments use ordinary List.foldr over the existing step constructor. The
accompanying certificate checks whole-body identity with the actual Lean reader;
these proposed terms carry no source claim on their own. -/

@[expose] public section

namespace SubtreeProofs.Rust.SourceEval.Evaluator

open LookupSource

def cacheHit : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 9,
    Action.assign 9 (Expr.use (Operand.move (Place.field (Place.local 4) (some 1) 0))),
    Action.storageLive 10,
    Action.storageLive 11,
    Action.assign 11 (Expr.use (Operand.move (Place.local 9))),
    Action.assign 10 (Expr.aggregate (Kind.optional) 1 [Operand.move (Place.local 11)]),
    Action.drop 11,
    Action.storageDead 11,
    Action.storageLive 12,
    Action.assign 12 (Expr.use (Operand.move (Place.local 3))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 10), Operand.move (Place.local 12)]),
    Action.drop 12,
    Action.storageDead 12,
    Action.drop 10,
    Action.storageDead 10,
    Action.drop 9,
    Action.storageDead 9,
    Action.drop 4,
    Action.storageDead 6,
    Action.storageDead 4]

def emptyLeft : Code :=
  List.foldr Control.Tree.step (.ret) [
    Action.storageLive 16,
    Action.storageLive 17,
    Action.assign 17 (Expr.aggregate (Kind.word) 0 []),
    Action.assign 16 (Expr.aggregate (Kind.embedding) 0 [Operand.move (Place.local 17), Operand.number 0]),
    Action.drop 17,
    Action.storageDead 17,
    Action.fakeRead (Place.local 16),
    Action.storageLive 18,
    Action.storageLive 19,
    Action.assign 19 (Expr.use (Operand.move (Place.local 3))),
    Action.storageLive 20,
    Action.assign 20 (Expr.address (Place.deref (Place.local 1))),
    Action.storageLive 21,
    Action.assign 21 (Expr.address (Place.deref (Place.local 2))),
    Action.storageLive 22,
    Action.storageLive 23,
    Action.assign 23 (Expr.address (Place.local 16)),
    Action.assign 22 (Expr.address (Place.deref (Place.local 23))),
    Action.call (Function.insert) [Operand.move (Place.local 19), Operand.move (Place.local 20), Operand.move (Place.local 21), Operand.move (Place.local 22)] 18,
    Action.storageDead 22,
    Action.storageDead 21,
    Action.storageDead 20,
    Action.storageDead 19,
    Action.fakeRead (Place.local 18),
    Action.storageDead 23,
    Action.storageLive 24,
    Action.storageLive 25,
    Action.assign 25 (Expr.use (Operand.move (Place.local 16))),
    Action.assign 24 (Expr.aggregate (Kind.optional) 1 [Operand.move (Place.local 25)]),
    Action.drop 25,
    Action.storageDead 25,
    Action.storageLive 26,
    Action.assign 26 (Expr.use (Operand.move (Place.local 18))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 24), Operand.move (Place.local 26)]),
    Action.drop 26,
    Action.storageDead 26,
    Action.drop 24,
    Action.storageDead 24,
    Action.drop 18,
    Action.storageDead 18,
    Action.drop 16,
    Action.storageDead 16,
    Action.storageDead 13,
    Action.drop 3,
    Action.storageDead 3,
    Action.storageDead 2,
    Action.storageDead 1]

def emptyRight : Code :=
  List.foldr Control.Tree.step (.ret) [
    Action.storageLive 16,
    Action.storageLive 17,
    Action.assign 17 (Expr.aggregate (Kind.word) 0 []),
    Action.assign 16 (Expr.aggregate (Kind.embedding) 0 [Operand.move (Place.local 17), Operand.number 0]),
    Action.drop 17,
    Action.storageDead 17,
    Action.fakeRead (Place.local 16),
    Action.storageLive 18,
    Action.storageLive 19,
    Action.assign 19 (Expr.use (Operand.move (Place.local 3))),
    Action.storageLive 20,
    Action.assign 20 (Expr.address (Place.deref (Place.local 1))),
    Action.storageLive 21,
    Action.assign 21 (Expr.address (Place.deref (Place.local 2))),
    Action.storageLive 22,
    Action.storageLive 23,
    Action.assign 23 (Expr.address (Place.local 16)),
    Action.assign 22 (Expr.address (Place.deref (Place.local 23))),
    Action.call (Function.insert) [Operand.move (Place.local 19), Operand.move (Place.local 20), Operand.move (Place.local 21), Operand.move (Place.local 22)] 18,
    Action.storageDead 22,
    Action.storageDead 21,
    Action.storageDead 20,
    Action.storageDead 19,
    Action.fakeRead (Place.local 18),
    Action.storageDead 23,
    Action.storageLive 24,
    Action.storageLive 25,
    Action.assign 25 (Expr.use (Operand.move (Place.local 16))),
    Action.assign 24 (Expr.aggregate (Kind.optional) 1 [Operand.move (Place.local 25)]),
    Action.drop 25,
    Action.storageDead 25,
    Action.storageLive 26,
    Action.assign 26 (Expr.use (Operand.move (Place.local 18))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 24), Operand.move (Place.local 26)]),
    Action.drop 26,
    Action.storageDead 26,
    Action.drop 24,
    Action.storageDead 24,
    Action.drop 18,
    Action.storageDead 18,
    Action.drop 16,
    Action.storageDead 16,
    Action.storageDead 13,
    Action.drop 3,
    Action.storageDead 3,
    Action.storageDead 2,
    Action.storageDead 1]

def unreachable : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.fakeRead (Place.local 13),
    Action.undefinedBehavior]

def headsFailure : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 39,
    Action.assign 39 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 40,
    Action.assign 40 (Expr.use (Operand.move (Place.local 32))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 39), Operand.move (Place.local 40)]),
    Action.drop 40,
    Action.storageDead 40,
    Action.drop 39,
    Action.storageDead 39]

def tailsFailure : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 49,
    Action.assign 49 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 50,
    Action.assign 50 (Expr.use (Operand.move (Place.local 42))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 49), Operand.move (Place.local 50)]),
    Action.drop 50,
    Action.storageDead 50,
    Action.drop 49,
    Action.storageDead 49]

def subtotalOverflow : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 56,
    Action.assign 56 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 57,
    Action.assign 57 (Expr.use (Operand.move (Place.local 42))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 56), Operand.move (Place.local 57)]),
    Action.drop 57,
    Action.storageDead 57,
    Action.drop 56,
    Action.storageDead 56,
    Action.storageDead 52]

def rootOverflow : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 62,
    Action.assign 62 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 63,
    Action.assign 63 (Expr.use (Operand.move (Place.local 42))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 62), Operand.move (Place.local 63)]),
    Action.drop 63,
    Action.storageDead 63,
    Action.drop 62,
    Action.storageDead 62,
    Action.storageDead 59]

def leftFailure : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 83,
    Action.assign 83 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 84,
    Action.assign 84 (Expr.use (Operand.move (Place.local 75))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 83), Operand.move (Place.local 84)]),
    Action.drop 84,
    Action.storageDead 84,
    Action.drop 83,
    Action.storageDead 83]

def finish : Code :=
  List.foldr Control.Tree.step (.ret) [
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

def rightFailure : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageLive 97,
    Action.assign 97 (Expr.aggregate (Kind.optional) 0 []),
    Action.storageLive 98,
    Action.assign 98 (Expr.use (Operand.move (Place.local 89))),
    Action.assign 0 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 97), Operand.move (Place.local 98)]),
    Action.drop 98,
    Action.storageDead 98,
    Action.drop 97,
    Action.storageDead 97,
    Action.storageDead 95,
    Action.drop 89,
    Action.storageDead 89,
    Action.drop 88,
    Action.storageDead 88,
    Action.drop 85,
    Action.storageDead 85,
    Action.drop 81]

def contractRight : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 88)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (.done) (finish) (rightFailure)) [
    Action.storageLive 82,
    Action.assign 82 (Expr.use (Operand.move (Place.field (Place.local 74) (some 1) 0))),
    Action.assign 81 (Expr.use (Operand.move (Place.local 82))),
    Action.drop 82,
    Action.storageDead 82,
    Action.fakeRead (Place.local 81),
    Action.storageLive 85,
    Action.storageLive 86,
    Action.assign 86 (Expr.address (Place.deref (Place.deref (Place.local 29)))),
    Action.storageLive 87,
    Action.assign 87 (Expr.address (Place.deref (Place.deref (Place.local 30)))),
    Action.call (Function.concatenate) [Operand.move (Place.local 86), Operand.move (Place.local 87)] 85,
    Action.storageDead 87,
    Action.storageDead 86,
    Action.fakeRead (Place.local 85),
    Action.storageLive 90,
    Action.storageLive 91,
    Action.assign 91 (Expr.address (Place.deref (Place.local 1))),
    Action.storageLive 92,
    Action.storageLive 93,
    Action.assign 93 (Expr.address (Place.local 85)),
    Action.assign 92 (Expr.address (Place.deref (Place.local 93))),
    Action.storageLive 94,
    Action.assign 94 (Expr.use (Operand.move (Place.local 75))),
    Action.call (Function.evaluate) [Operand.move (Place.local 91), Operand.move (Place.local 92), Operand.move (Place.local 94)] 90,
    Action.storageDead 94,
    Action.storageDead 92,
    Action.storageDead 91,
    Action.storageLive 88,
    Action.assign 88 (Expr.use (Operand.move (Place.field (Place.local 90) none 0))),
    Action.storageLive 89,
    Action.assign 89 (Expr.use (Operand.move (Place.field (Place.local 90) none 1))),
    Action.drop 90,
    Action.storageDead 93,
    Action.storageDead 90,
    Action.storageLive 95]

def cleanupLeft : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageDead 81,
    Action.drop 75,
    Action.storageDead 75,
    Action.drop 74,
    Action.storageDead 74,
    Action.drop 71,
    Action.storageDead 71,
    Action.drop 64,
    Action.storageDead 64]

def contractLeft : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 74)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (leftFailure) (contractRight) (cleanupLeft)) [
    Action.storageLive 61,
    Action.assign 61 (Expr.use (Operand.copy (Place.field (Place.local 59) (some 1) 0))),
    Action.assign 58 (Expr.use (Operand.copy (Place.local 61))),
    Action.storageDead 61,
    Action.fakeRead (Place.local 58),
    Action.storageDead 59,
    Action.storageLive 64,
    Action.storageLive 65,
    Action.storageLive 66,
    Action.storageLive 67,
    Action.assign 67 (Expr.use (Operand.move (Place.field (Place.local 37) none 0))),
    Action.call (Function.boxNew) [Operand.move (Place.local 67)] 66,
    Action.storageDead 67,
    Action.storageLive 68,
    Action.storageLive 69,
    Action.assign 69 (Expr.use (Operand.move (Place.field (Place.local 47) none 0))),
    Action.call (Function.boxNew) [Operand.move (Place.local 69)] 68,
    Action.storageDead 69,
    Action.assign 65 (Expr.aggregate (Kind.word) 1 [Operand.move (Place.local 66), Operand.move (Place.local 68)]),
    Action.drop 68,
    Action.storageDead 68,
    Action.drop 66,
    Action.storageDead 66,
    Action.storageLive 70,
    Action.assign 70 (Expr.use (Operand.copy (Place.local 58))),
    Action.assign 64 (Expr.aggregate (Kind.embedding) 0 [Operand.move (Place.local 65), Operand.move (Place.local 70)]),
    Action.storageDead 70,
    Action.drop 65,
    Action.storageDead 65,
    Action.fakeRead (Place.local 64),
    Action.storageLive 71,
    Action.storageLive 72,
    Action.assign 72 (Expr.address (Place.deref (Place.deref (Place.local 27)))),
    Action.storageLive 73,
    Action.assign 73 (Expr.address (Place.deref (Place.deref (Place.local 28)))),
    Action.call (Function.concatenate) [Operand.move (Place.local 72), Operand.move (Place.local 73)] 71,
    Action.storageDead 73,
    Action.storageDead 72,
    Action.fakeRead (Place.local 71),
    Action.storageLive 76,
    Action.storageLive 77,
    Action.storageLive 78,
    Action.assign 78 (Expr.address (Place.local 71)),
    Action.assign 77 (Expr.address (Place.deref (Place.local 78))),
    Action.storageLive 79,
    Action.assign 79 (Expr.address (Place.deref (Place.local 2))),
    Action.storageLive 80,
    Action.assign 80 (Expr.use (Operand.move (Place.local 42))),
    Action.call (Function.evaluate) [Operand.move (Place.local 77), Operand.move (Place.local 79), Operand.move (Place.local 80)] 76,
    Action.storageDead 80,
    Action.storageDead 79,
    Action.storageDead 77,
    Action.storageLive 74,
    Action.assign 74 (Expr.use (Operand.move (Place.field (Place.local 76) none 0))),
    Action.storageLive 75,
    Action.assign 75 (Expr.use (Operand.move (Place.field (Place.local 76) none 1))),
    Action.drop 76,
    Action.storageDead 78,
    Action.storageDead 76,
    Action.storageLive 81]

def cleanupSubtotal : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageDead 58]

def addRoot : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 59)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (rootOverflow) (contractLeft) (cleanupSubtotal)) [
    Action.storageLive 55,
    Action.assign 55 (Expr.use (Operand.copy (Place.field (Place.local 52) (some 1) 0))),
    Action.assign 51 (Expr.use (Operand.copy (Place.local 55))),
    Action.storageDead 55,
    Action.fakeRead (Place.local 51),
    Action.storageDead 52,
    Action.storageLive 58,
    Action.storageLive 59,
    Action.storageLive 60,
    Action.assign 60 (Expr.use (Operand.copy (Place.local 51))),
    Action.call (Function.checkedAdd) [Operand.move (Place.local 60), Operand.number 1] 59,
    Action.storageDead 60]

def cleanupTails : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageDead 51,
    Action.drop 47]

def addScores : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 52)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (subtotalOverflow) (addRoot) (cleanupTails)) [
    Action.storageLive 48,
    Action.assign 48 (Expr.use (Operand.move (Place.field (Place.local 41) (some 1) 0))),
    Action.assign 47 (Expr.use (Operand.move (Place.local 48))),
    Action.drop 48,
    Action.storageDead 48,
    Action.fakeRead (Place.local 47),
    Action.storageLive 51,
    Action.storageLive 52,
    Action.storageLive 53,
    Action.assign 53 (Expr.use (Operand.copy (Place.field (Place.local 37) none 1))),
    Action.storageLive 54,
    Action.assign 54 (Expr.use (Operand.copy (Place.field (Place.local 47) none 1))),
    Action.call (Function.checkedAdd) [Operand.move (Place.local 53), Operand.move (Place.local 54)] 52,
    Action.storageDead 54,
    Action.storageDead 53]

def cleanupHeads : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageDead 47,
    Action.drop 42,
    Action.storageDead 42,
    Action.drop 41,
    Action.storageDead 41,
    Action.drop 37]

def recurseTails : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 41)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (tailsFailure) (addScores) (cleanupHeads)) [
    Action.storageLive 38,
    Action.assign 38 (Expr.use (Operand.move (Place.field (Place.local 31) (some 1) 0))),
    Action.assign 37 (Expr.use (Operand.move (Place.local 38))),
    Action.drop 38,
    Action.storageDead 38,
    Action.fakeRead (Place.local 37),
    Action.storageLive 43,
    Action.storageLive 44,
    Action.assign 44 (Expr.address (Place.deref (Place.deref (Place.local 28)))),
    Action.storageLive 45,
    Action.assign 45 (Expr.address (Place.deref (Place.deref (Place.local 30)))),
    Action.storageLive 46,
    Action.assign 46 (Expr.use (Operand.move (Place.local 32))),
    Action.call (Function.evaluate) [Operand.move (Place.local 44), Operand.move (Place.local 45), Operand.move (Place.local 46)] 43,
    Action.storageDead 46,
    Action.storageDead 45,
    Action.storageDead 44,
    Action.storageLive 41,
    Action.assign 41 (Expr.use (Operand.move (Place.field (Place.local 43) none 0))),
    Action.storageLive 42,
    Action.assign 42 (Expr.use (Operand.move (Place.field (Place.local 43) none 1))),
    Action.drop 43,
    Action.storageDead 43,
    Action.storageLive 47]

def cleanupInputs : Code :=
  List.foldr Control.Tree.step (.done) [
    Action.storageDead 37,
    Action.drop 32,
    Action.storageDead 32,
    Action.drop 31,
    Action.storageDead 31,
    Action.storageDead 30,
    Action.storageDead 29,
    Action.storageDead 28,
    Action.storageDead 27,
    Action.storageDead 13]

def recurseHeads : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 31)) [(Key.variant (Kind.optional) 0, 0), (Key.variant (Kind.optional) 1, 1)] (none) (headsFailure) (recurseTails) (cleanupInputs)) [
    Action.storageLive 27,
    Action.assign 27 (Expr.address (Place.field (Place.deref (Place.field (Place.local 13) none 0)) (some 1) 0)),
    Action.storageLive 28,
    Action.assign 28 (Expr.address (Place.field (Place.deref (Place.field (Place.local 13) none 0)) (some 1) 1)),
    Action.storageLive 29,
    Action.assign 29 (Expr.address (Place.field (Place.deref (Place.field (Place.local 13) none 1)) (some 1) 0)),
    Action.storageLive 30,
    Action.assign 30 (Expr.address (Place.field (Place.deref (Place.field (Place.local 13) none 1)) (some 1) 1)),
    Action.storageLive 33,
    Action.storageLive 34,
    Action.assign 34 (Expr.address (Place.deref (Place.deref (Place.local 27)))),
    Action.storageLive 35,
    Action.assign 35 (Expr.address (Place.deref (Place.deref (Place.local 29)))),
    Action.storageLive 36,
    Action.assign 36 (Expr.use (Operand.move (Place.local 3))),
    Action.call (Function.evaluate) [Operand.move (Place.local 34), Operand.move (Place.local 35), Operand.move (Place.local 36)] 33,
    Action.storageDead 36,
    Action.storageDead 35,
    Action.storageDead 34,
    Action.storageLive 31,
    Action.assign 31 (Expr.use (Operand.move (Place.field (Place.local 33) none 0))),
    Action.storageLive 32,
    Action.assign 32 (Expr.use (Operand.move (Place.field (Place.local 33) none 1))),
    Action.drop 33,
    Action.storageDead 33,
    Action.storageLive 37]

def leftPairCheck : Code :=
  .switch (Scrutinee.discriminant (Place.deref (Place.field (Place.local 13) none 0))) [(Key.variant (Kind.word) 1, 0)] (some 1) (.done) (unreachable) (recurseHeads)

def rightCases : Code :=
  .switch (Scrutinee.discriminant (Place.deref (Place.field (Place.local 13) none 1))) [(Key.variant (Kind.word) 0, 0), (Key.variant (Kind.word) 1, 1)] (none) (emptyRight) (leftPairCheck) (.done)

def cacheMiss : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.deref (Place.field (Place.local 13) none 0))) [(Key.variant (Kind.word) 0, 0)] (some 1) (emptyLeft) (rightCases) (.done)) [
    Action.drop 4,
    Action.storageDead 6,
    Action.storageDead 4,
    Action.storageLive 13,
    Action.storageLive 14,
    Action.assign 14 (Expr.use (Operand.copy (Place.local 1))),
    Action.storageLive 15,
    Action.assign 15 (Expr.use (Operand.copy (Place.local 2))),
    Action.assign 13 (Expr.aggregate (Kind.tuple) 0 [Operand.move (Place.local 14), Operand.move (Place.local 15)]),
    Action.storageDead 15,
    Action.storageDead 14]

def returnResult : Code :=
  List.foldr Control.Tree.step (.ret) [
    Action.drop 3,
    Action.storageDead 3,
    Action.storageDead 2,
    Action.storageDead 1]

def start : Code :=
  List.foldr Control.Tree.step (.switch (Scrutinee.discriminant (Place.local 4)) [(Key.variant (Kind.optional) 1, 0)] (some 1) (cacheHit) (cacheMiss) (returnResult)) [
    Action.storageLive 0,
    Action.storageLive 4,
    Action.storageLive 5,
    Action.storageLive 6,
    Action.assign 6 (Expr.address (Place.local 3)),
    Action.assign 5 (Expr.address (Place.deref (Place.local 6))),
    Action.storageLive 7,
    Action.assign 7 (Expr.address (Place.deref (Place.local 1))),
    Action.storageLive 8,
    Action.assign 8 (Expr.address (Place.deref (Place.local 2))),
    Action.call (Function.lookup) [Operand.move (Place.local 5), Operand.move (Place.local 7), Operand.move (Place.local 8)] 4,
    Action.storageDead 8,
    Action.storageDead 7,
    Action.storageDead 5]

def body : Code := start

end SubtreeProofs.Rust.SourceEval.Evaluator
