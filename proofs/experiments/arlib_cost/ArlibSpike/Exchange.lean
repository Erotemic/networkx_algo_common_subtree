import Arlib.Computation.Dict
import Arlib.Computation.Std

namespace ArlibSpike
open Arlib.Computation

/-- One abstract dictionary lookup is one dictionary operation, not a word-RAM
lookup theorem. Carrier size and the chosen implementation model are explicit. -/
theorem dictionary_find_steps {K V : Type} [DecidableEq K] (key : K) (d : Dict K V) :
    Charged.steps (Rate.unit StdOp) (Dict.find key d : Charged StdOp Cell (Option V)) = 1 := by
  simp [Charged.steps]

theorem dictionary_find_listBacked {K V : Type} [DecidableEq K]
    (key : K) (d : Dict K V) (setup : Nat) :
    Charged.steps CostModel.unitCost
      (Charged.exchange ((StdImpl.listBacked setup).atSize d.card)
        (Dict.find key d : Charged StdOp Cell (Option V))) ≤ 3 * d.card + setup + 1 := by
  simpa [dictionary_find_steps] using (StdImpl.listBacked setup).wordSteps_le d.card
    (Dict.find key d : Charged StdOp Cell (Option V))

/-- A separate explicitly assumed constant-cost model; this is not expected
hashing and supplies no implementation/collision-distribution theorem. -/
theorem dictionary_find_constantTime {K V : Type} [DecidableEq K]
    (key : K) (d : Dict K V) (setup : Nat) :
    Charged.steps CostModel.unitCost
      (Charged.exchange ((StdImpl.constantTime setup).atSize d.card)
        (Dict.find key d : Charged StdOp Cell (Option V))) ≤ setup + 1 := by
  simpa [dictionary_find_steps] using (StdImpl.constantTime setup).wordSteps_le d.card
    (Dict.find key d : Charged StdOp Cell (Option V))

end ArlibSpike
