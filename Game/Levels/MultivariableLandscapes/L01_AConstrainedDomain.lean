import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 1
Title "A constrained domain"

Introduction "Objective: Express and verify a domain with explicit inequalities.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity.\n\nFor √(4-x²-y²)/(x-y), a real-valued geometric domain requires x²+y²≤4 and x-y≠0. At (1,0), these are two concrete checks. `∧` collects the independent restrictions. Lean defines division and square root on all real inputs, so recording the intended domain is part of the mathematics.\n\nWorked example: For √(9-x²-y²)/(x+y), the point (2,1) meets 2²+1²≤9 and 2+1≠0. Both domain checks are necessary.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Express and verify a domain with explicit inequalities. -/
Statement exercise_MultivariableLandscapes_1 : (1:ℝ)^2 + 0^2 ≤ 4 ∧ (1:ℝ) ≠ 0 := by
  Hint "1. Separate the radicand restriction from the denominator restriction."
  Hint (hidden := true) "2. Substitute x=1 and y=0."
  Hint (hidden := true) "3. Check each numerical condition."
  constructor
  · norm_num
  · norm_num

Conclusion "The proposed point meets both the square-root and denominator domain restrictions."
