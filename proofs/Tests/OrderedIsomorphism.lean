import SubtreeProofs.Paper2004.IsomorphismScores
import SubtreeProofs.Paper2004.DynamicProgram
import SubtreeProofs.Paper2004.AffinityIsomorphismDP
import Mathlib.Data.Int.Basic

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

namespace AffinityIsomorphismTests

open SubtreeProofs.Paper2004.AnnotatedIso

def left : Word Nat := .node 0 (.node 1 .nil .nil) .nil
def right : Word Nat := .node 10 .nil .nil
def affinity (u v : Nat) : ℤ := if u = 1 ∧ v = 10 then 7 else 0

-- A forbidden outer pair does not promote a grandchild in fixed-parent mode.
example : AffinityDP.level affinity left right = .nil := by decide +kernel
example : score affinity (AffinityDP.level affinity left right) = 0 := by decide +kernel

-- General mode may move its parent region and retains original node identities.
example : leftProjection (AffinityDP.anywhere affinity left right) = .node 1 .nil .nil := by decide +kernel
example : rightProjection (AffinityDP.anywhere affinity left right) = .node 10 .nil .nil := by decide +kernel
example : score affinity (AffinityDP.anywhere affinity left right) = 7 := by decide +kernel

-- Zero affinity forbids selecting a pair, even when its scalar score is tied.
example : AffinityDP.level (fun (_ _ : Nat) => (0 : ℤ)) right right = .nil := by decide +kernel

end AffinityIsomorphismTests
