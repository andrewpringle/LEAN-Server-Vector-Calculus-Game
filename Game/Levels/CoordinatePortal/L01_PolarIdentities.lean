import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 1
Title "Polar identities"

Introduction "Objective: Verify the radial identity for polar coordinates.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities.\n\nPolar coordinates use x=r cos θ and y=r sin θ. Factor out r² and use sin²θ+cos²θ=1. The identity holds for all real r and θ; using polar coordinates as a single-cover region additionally requires r≥0 and an angular interval of length 2π, with the usual exceptional origin and boundary.\n\nWorked example: When r=2, (2 cos θ)²+(2 sin θ)²=4(sin²θ+cos²θ)=4. The variable-radius proof uses the same factorization.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Verify the radial identity for polar coordinates. -/
Statement exercise_CoordinatePortal_1 (r t : ℝ) : (r*Real.cos t)^2+(r*Real.sin t)^2 = r^2 := by
  Hint "1. Name the factorization of the two coordinate squares."
  Hint (hidden := true) "2. Rewrite the trigonometric factor with `Real.sin_sq_add_cos_sq`."
  Hint (hidden := true) "3. Finish the remaining polynomial identity."
  have factor : (r*Real.cos t)^2+(r*Real.sin t)^2 = r^2*(Real.sin t^2+Real.cos t^2) := by ring
  rw [factor, Real.sin_sq_add_cos_sq]
  ring

Conclusion "The polar coordinate identity preserves squared radius."
