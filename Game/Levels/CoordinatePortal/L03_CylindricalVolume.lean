import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 3
Title "Cylindrical volume"

Introduction "Objective: Evaluate a correctly weighted cylindrical-coordinate integral.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities. Earlier levels of Coordinate Portal.\n\nFor a unit-radius cylinder of height 2, the cylindrical volume factor is r on 0≤r≤1 and 0≤θ≤2π. Integrate the vertical coordinate first to get 2r, then the radial coordinate to get 1, then the angle. The factor is the nonnegative absolute Jacobian on this domain. The formal goal is the coordinate-side volume integral.\n\nExercise: prove the statement below."

/-- A constant real factor may be pulled outside an interval integral. -/
TheoremDoc intervalIntegral.integral_const_mul as "integral_const_mul" in "Calculus"
NewTheorem intervalIntegral.integral_const_mul

/-- Evaluate a correctly weighted cylindrical-coordinate integral. -/
Statement exercise_CoordinatePortal_3 : (∫ t : ℝ in 0..(2*Real.pi), ∫ r : ℝ in 0..1, ∫ z : ℝ in 0..2, r) = 2*Real.pi := by
  Hint "1. Calculate the vertical integral for a fixed radius."
  Hint (hidden := true) "2. Pull the constant 2 out of the radial integral and integrate r."
  Hint (hidden := true) "3. Integrate the resulting constant over the angular interval."
  have vertical (r : ℝ) : (∫ z : ℝ in 0..2, r) = 2*r := by
    rw [constant_integral]
    ring
  have radial : (∫ r : ℝ in 0..1, ∫ z : ℝ in 0..2, r) = 1 := by
    rw [integral_values vertical, intervalIntegral.integral_const_mul, integral_id]
    norm_num
  rw [radial, constant_integral]
  ring

Conclusion "The cylindrical coordinate-side volume integral evaluates to 2π with its radial factor."
