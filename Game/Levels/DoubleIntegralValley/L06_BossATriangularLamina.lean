import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 6
Title "Boss: a triangular lamina"

Introduction "Objective: Combine variable bounds, mass, and a first moment.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments. Earlier levels of Double Integral Valley.\n\nFor uniform density on 0≤y≤x≤1, derive the inner mass and moment integrals as x, x², and x²/2. Integrating these gives mass 1/2 and moments 1/3 and 1/6. Divide by the positive mass to obtain the full centroid (2/3,1/3). Reuse pointwise replacement and the power rule; the boss introduces no new proof syntax.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Integrate a natural power using the next power divided by the next exponent. -/
TheoremDoc integral_pow as "integral_pow" in "Calculus"
/-- Division by a fixed scalar commutes with interval integration. -/
TheoremDoc intervalIntegral.integral_div as "integral_div" in "Calculus"
NewTheorem integral_pow intervalIntegral.integral_div

/-- Combine variable bounds, mass, and a first moment. -/
Statement exercise_DoubleIntegralValley_6 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..x, (1:ℝ)) = 1/2 ∧ (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..x, x) / (1/2) = 2/3 ∧ (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..x, y) / (1/2) = 1/3 := by
  Hint "1. For each quantity, name its inner integral as a formula in x."
  Hint (hidden := true) "2. Use `integral_values` to replace it under the outer integral."
  Hint (hidden := true) "3. Use `integral_id` or `integral_pow`, and normalize the moments by mass 1/2."
  constructor
  · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, (1:ℝ)) = x := by
      rw [constant_integral]
      ring
    rw [integral_values innerValue, integral_id]
    norm_num
  · constructor
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, x) = x^2 := by
        rw [constant_integral]
        ring
      rw [integral_values innerValue, integral_pow]
      norm_num
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, y) = x^2/2 := by
        rw [integral_id]
        ring
      rw [integral_values innerValue, intervalIntegral.integral_div, integral_pow]
      norm_num

Conclusion "The triangular lamina has mass 1/2 and centroid (2/3,1/3)."
