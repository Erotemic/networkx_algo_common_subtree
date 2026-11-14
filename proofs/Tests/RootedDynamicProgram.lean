import SubtreeProofs.Droschinsky2018.RootedDynamicProgram

namespace RootedDPTests

open SubtreeProofs SubtreeProofs.Droschinsky2016 SubtreeProofs.Droschinsky2018

def discriminatorWeights : Scoring (Fin 2) (Fin 3) ℤ where
  node u v := if (u = 0 ∧ v = 0) ∨ (u = 1 ∧ v = 2) then 4 else ⊥
  edge _ _ := 400

def leftChildren (u : Fin 2) : List (Fin 2) := if u = 0 then [1] else []
def rightChildren (v : Fin 3) : List (Fin 3) := if v = 0 then [1] else if v = 1 then [2] else []

example : RootedDP.rootedOptimum [0,1] [0,1,2] leftChildren rightChildren discriminatorWeights 1 = 7 := by decide
example : RootedDP.rootedOptimum [0,1] [0,1,2] leftChildren rightChildren discriminatorWeights ⊤ = 4 := by decide
example : RootedDP.rootedOptimum [0] [0] (fun (_ : Fin 1) => []) (fun (_ : Fin 1) => [])
  ({node := fun _ _ => ((-4 : ℤ) : WithBot ℤ), edge := fun _ _ => 0} : Scoring (Fin 1) (Fin 1) ℤ) 1 = ((-4 : ℤ) : WithBot ℤ) := by decide

example : RootedDP.rootedOptimum [0] [0] (fun (_ : Fin 1) => []) (fun (_ : Fin 1) => [])
  ({node := fun _ _ => ⊥, edge := fun _ _ => 0} : Scoring (Fin 1) (Fin 1) ℤ) 1 = ⊥ := by decide

end RootedDPTests
