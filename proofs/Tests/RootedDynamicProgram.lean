import SubtreeProofs.Droschinsky2018.RootedDynamicProgram
import SubtreeProofs.Droschinsky2016.RootedDynamicProgram

namespace RootedDPTests

open SubtreeProofs SubtreeProofs.Droschinsky2016 SubtreeProofs.Droschinsky2018

def discriminatorWeights : Scoring (Fin 2) (Fin 3) ℤ where
  node u v := if (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 2) then 4 else ⊥
  edge _ _ := 400

def leftChildren (u : Fin 2) : List (Fin 2) := if u = 0 then [1] else []
def rightChildren (v : Fin 3) : List (Fin 3) := if v = 0 then [1] else if v = 1 then [2] else []

example : Droschinsky2018.RootedDP.rootedOptimum [0,1] [0,1,2] leftChildren rightChildren discriminatorWeights 1 = 7 := by decide
example : Droschinsky2018.RootedDP.rootedOptimum [0,1] [0,1,2] leftChildren rightChildren discriminatorWeights ⊤ = 4 := by decide
example : Droschinsky2018.RootedDP.rootedOptimum [0] [0] (fun (_ : Fin 1) => []) (fun (_ : Fin 1) => [])
  ({node := fun _ _ => ((-4 : ℤ) : WithBot ℤ), edge := fun _ _ => 0} : Scoring (Fin 1) (Fin 1) ℤ) 1 = ((-4 : ℤ) : WithBot ℤ) := by decide

example : Droschinsky2018.RootedDP.rootedOptimum [0] [0] (fun (_ : Fin 1) => []) (fun (_ : Fin 1) => [])
  ({node := fun _ _ => ⊥, edge := fun _ _ => 0} : Scoring (Fin 1) (Fin 1) ℤ) 1 = ⊥ := by decide

-- Connected isomorphisms cannot skip the incompatible middle vertex.
example : Droschinsky2016.RootedDP.read
    (Droschinsky2016.RootedDP.solve [0,1] [0,1,2] leftChildren rightChildren discriminatorWeights) 0 0 = 4 := by decide

-- A direct matched edge keeps its edge reward in the isomorphism problem.
example : Droschinsky2016.RootedDP.read
    (Droschinsky2016.RootedDP.solve [0,1] [0,1] leftChildren leftChildren
      ({node := fun _ _ => 4, edge := fun _ _ => 400} : Scoring (Fin 2) (Fin 2) ℤ)) 0 0 = 408 := by decide

example : Droschinsky2016.RootedDP.read
    (Droschinsky2016.RootedDP.solve [0] [0] (fun (_ : Fin 1) => []) (fun (_ : Fin 1) => [])
      ({node := fun _ _ => ((-4 : ℤ) : WithBot ℤ), edge := fun _ _ => 0} : Scoring (Fin 1) (Fin 1) ℤ)) 0 0 =
    ((-4 : ℤ) : WithBot ℤ) := by decide

-- Both orientations of a two-vertex input are supplied explicitly.
def bothOrientations (root u : Fin 2) : List (Fin 2) :=
  if u = root then if root = 0 then [1] else [0] else []

example : Droschinsky2016.RootedDP.unrootedOptimum [0,1] [0,1] leftChildren bothOrientations
    ({node := fun _ _ => 4, edge := fun _ _ => 400} : Scoring (Fin 2) (Fin 2) ℤ) = 408 := by decide

example : Droschinsky2018.RootedDP.unrootedOptimum [0,1] [0,1] bothOrientations bothOrientations
    ({node := fun _ _ => 4, edge := fun _ _ => 400} : Scoring (Fin 2) (Fin 2) ℤ) 1 = 408 := by decide

end RootedDPTests
