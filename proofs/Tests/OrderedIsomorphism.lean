import SubtreeProofs.Paper2004.IsomorphismScores
import SubtreeProofs.Paper2004.DynamicProgram

namespace OrderedIsomorphismTests

open SubtreeProofs.Paper2004.OrderedTree

-- A freely chosen root can recover the full fork below a unary input root.
example : OrderedIsoDP.levelSize fork.children (node [fork]).children = 1 := by decide +kernel
example : OrderedIsoDP.anywhereSize fork.children (node [fork]).children = 2 := by decide +kernel

-- Contracting the first internal edge merges two child lists, producing a
-- three-leaf star. Adjacency-preserving subtree selection cannot do this.
def threeLeaves : SubtreeProofs.Paper2004.OrderedTree := .node [singleton,singleton,singleton]
def branched : SubtreeProofs.Paper2004.OrderedTree := .node [fork,singleton]

example : OrderedIsoDP.anywhereSize threeLeaves.children branched.children = 2 := by decide +kernel
example : paperLcs threeLeaves.encodeDyck branched.encodeDyck = 3 := by decide +kernel

example : Embeds threeLeaves branched := by
  apply embeds_of_step
  simpa only [threeLeaves,branched,fork,children,List.nil_append,List.singleton_append,List.cons_append] using
    (ContractStep.atRoot [] [singleton] fork)

example : ¬ IsomorphicSubtree threeLeaves branched := by
  intro h
  have hu := (OrderedIsoDP.anywhereSize_optimum threeLeaves branched).2 threeLeaves
    (RootPrunes.refl threeLeaves).isomorphicSubtree h
  have hs : OrderedIsoDP.anywhereSize threeLeaves.children branched.children = 2 := by decide +kernel
  rw [hs] at hu
  have he : threeLeaves.edgeCount = 3 := rfl
  rw [he] at hu
  omega

end OrderedIsomorphismTests
