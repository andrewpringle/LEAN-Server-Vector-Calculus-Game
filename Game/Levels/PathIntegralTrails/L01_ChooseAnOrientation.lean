import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 1
Title "Choose an orientation"

Introduction "Objective: Parametrize a line segment with specified initial and final points.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus.\n\nThe segment (1-t)A+tB runs from A at parameter 0 to B at parameter 1. Its order gives the path orientation. Verify the endpoint identities using scalar-multiplication identities; `simp` removes the zero and unit coefficients.\n\nWorked example: The segment from (0,0,0) to (2,0,0) has midpoint (1,0,0) at t=1/2, start at t=0, and finish at t=1.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Parametrize a line segment with specified initial and final points. -/
Statement exercise_PathIntegralTrails_1 (A B : Vec) : (fun t : ℝ => (1-t) • A + t • B) 0 = A ∧ (fun t : ℝ => (1-t) • A + t • B) 1 = B := by
  Hint "1. Separate the initial and final endpoint."
  Hint (hidden := true) "2. Substitute t=0 and simplify."
  Hint (hidden := true) "3. Substitute t=1 and simplify."
  constructor
  · simp
  · simp

Conclusion "The segment parametrization runs from A to B in the stated orientation."
