import SubtreeProofs.Paper2004.RationalOrderedSolver

open SubtreeProofs.Paper2004.AnnotatedIso
open RationalSolver

def first : Input := .node 0 (.node 1 .nil .nil) .nil
def second : Input := .node 10 .nil .nil
def affinity (a b : Nat) : ℚ := if a = 1 ∧ b = 10 then 7/3 else 0

example : solveResult affinity true first second = (.nil,0) := by
  rw [solveResult, solve_eq]
  decide +kernel
example : solveResult affinity false first second = (.node (1,10) .nil .nil,7/3) := by
  rw [solveResult, solve_eq]
  decide +kernel

example : IsMaximumAny affinity (solve affinity false first second) first second :=
  solve_correct affinity false first second

example : ((vertices (solve affinity false first second)).map Prod.fst).Nodup ∧
    ((vertices (solve affinity false first second)).map Prod.snd).Nodup := by
  exact solve_unique_endpoints affinity false first second (by decide +kernel) (by decide +kernel)

example : solve (fun _ _ => (0 : ℚ)) false first second = .nil := by
  rw [solve_eq]
  decide +kernel

example : (solveResult (fun _ _ => (2^200 + 1 : ℚ)) true second second).2 = 2^200+1 := by
  rw [solveResult, solve_eq]
  decide +kernel

#print axioms solveResult_correct
#print axioms solve_unique_endpoints
