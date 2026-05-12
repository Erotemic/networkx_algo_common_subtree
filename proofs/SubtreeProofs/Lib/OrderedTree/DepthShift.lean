import SubtreeProofs.Lib.OrderedTree.Core

namespace SubtreeProofs.Lib.OrderedTree
namespace Tree

/--
Conversion between depth conventions:
`depth1 = depth0 + 1` for all ordered rooted trees.
-/
theorem depth1_eq_depth0_add_one (t : Tree) :
    depth1 t = depth0 t + 1 := by
  have hpos : 1 ≤ depth1 t := depth1_pos t
  have h : depth1 t = (depth1 t - 1) + 1 := (Nat.sub_eq_iff_eq_add hpos).1 rfl
  simpa [depth0] using h

/-- Equivalent restatement of depth convention conversion. -/
theorem depth0_eq_depth1_sub_one (t : Tree) :
    depth0 t = depth1 t - 1 := by
  rfl

end Tree
end SubtreeProofs.Lib.OrderedTree
