import SubtreeProofs.Paper2004.RationalOrderedSolver
import Lean.Data.Json

/-! JSON transport for the compiled, proved exact solver. Serialization and
process I/O are tested integration boundaries; the solver is not reimplemented. -/

open Lean
open SubtreeProofs.Paper2004.AnnotatedIso
open RationalSolver

private partial def decodeWord (json : Json) : Except String Input := do
  let values ← json.getArr?
  if values.isEmpty then return .nil
  unless values.size == 3 do throw "a forest node must contain identity, head and tail"
  return .node (← values[0]!.getNat?) (← decodeWord values[1]!) (← decodeWord values[2]!)

private def decodeWeight (json : Json) : Except String Rat := do
  let pair ← json.getArr?
  unless pair.size == 2 do throw "a rational must contain numerator and denominator strings"
  let some num := (← pair[0]!.getStr?).toInt? | throw "invalid rational numerator"
  let some den := (← pair[1]!.getStr?).toNat? | throw "invalid rational denominator"
  unless den > 0 do throw "rational denominator must be positive"
  unless num ≥ 0 do throw "affinities must be nonnegative"
  return mkRat num den

private def pairs : Witness → List (Nat × Nat)
  | .nil => []
  | .node label head tail => label :: (pairs head ++ pairs tail)

private def process (json : Json) : Except String Json := do
  let version ← (← json.getObjVal? "protocol").getNat?
  unless version == 1 do throw "unsupported exact ordered protocol"
  let left ← decodeWord (← json.getObjVal? "left")
  let right ← decodeWord (← json.getObjVal? "right")
  let rooted ← (← json.getObjVal? "rooted").getBool?
  let weights ← (← (← json.getObjVal? "weights").getArr?).mapM fun row => do
    (← row.getArr?).mapM decodeWeight
  unless weights.size == left.numNodes do throw "affinity matrix row count does not match input"
  unless weights.all (·.size == right.numNodes) do throw "affinity matrix column count does not match input"
  unless (vertices left).all (· < left.numNodes) &&
      (vertices right).all (· < right.numNodes) do throw "original identity outside affinity matrix"
  let affinity := fun a b => (weights[a]?.getD #[])[b]?.getD 0
  let (witness,value) := solveResult affinity rooted left right
  let ids := (pairs witness).toArray.map fun (a,b) => Json.arr #[toJson a,toJson b]
  return Json.mkObj [("protocol",toJson (1 : Nat)), ("pairs",.arr ids),
    ("numerator",toJson (toString value.num)), ("denominator",toJson (toString value.den))]

def main : IO UInt32 := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  repeat
    let line ← stdin.getLine
    if line.isEmpty then break
    let output := do process (← Json.parse line)
    let response := match output with
      | .ok json => json
      | .error error => Json.mkObj [("error",toJson error)]
    stdout.putStrLn response.compress
    stdout.flush
  return 0
