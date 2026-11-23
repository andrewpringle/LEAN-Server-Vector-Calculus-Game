import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 1
Title "Endpoints of a curve"

Introduction "Objective: Evaluate a polynomial curve at its parameter endpoints.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration.\n\n`fun t => ...` describes a function of the parameter t. A curve assigns a spatial point to each t in its parameter interval. Here the endpoints come from substituting 0 and 1. Use the same component-comparison method as for vector addition.\n\nWorked example: For c(t)=(t,2t,1) on [0,1], substitute t=0 and t=1 to find (0,0,1) and (1,2,1).\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Evaluate a polynomial curve at its parameter endpoints. -/
Statement exercise_CurveNavigator_1 : (fun t : ℝ => (![t,t^2,0] : Vec)) 0 = ![0,0,0] ∧ (fun t : ℝ => (![t,t^2,0] : Vec)) 1 = ![1,1,0] := by
  Hint "1. Separate the initial and final endpoint."
  Hint (hidden := true) "2. Apply `vector_eq` in each part."
  Hint (hidden := true) "3. Substitute the parameter and calculate each coordinate."
  constructor
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num

Conclusion "The parametrization has the stated initial and final points."
