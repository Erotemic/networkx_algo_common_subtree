/- Smoke program adapted from arlib's ArlibTest/Computation/ChargedAuthoring.lean.
Copyright (c) 2026 Kuldeep S. Meel. Apache-2.0; see LICENSE.arlib.
Upstream revision: 8d08f89a6d05c5e8368e91659bd6e117fbb74c4e. -/
import ArlibSpike.MemoLookup
import ArlibSpike.Exchange
import ArlibSpike.SourceExecution
import Arlib.Computation.Charged
import Arlib.Computation.Dict
import Arlib.Computation.Std
import Arlib.Computation.ChargedStorage
import Arlib.Computation.ChargedCopy
import SubtreeProofs

namespace ArlibSpike
open Arlib.Computation

def source : Charged Op Unit (Word 8) := do
  let n ← ChargedWord.literal 3
  let v ← ChargedVector.allocate n
  let x ← ChargedWord.literal 7
  let v ← ChargedVector.fill 3 n v x
  let zero ← ChargedWord.literal 0
  ChargedVector.read v zero

example : source.val.toNat = 7 := by rfl
example : Charged.steps CostModel.unitCost source = 23 := by decide

end ArlibSpike
