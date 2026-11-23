import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 5
Title "A lamina centroid"

Introduction "Objective: Compute mass and a normalized first moment.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments. Earlier levels of Double Integral Valley.\n\nThe uniform rectangle [0,2]×[0,1] has positive mass 2. Its centroid coordinates are the first moments divided by that mass. For the x moment, x is constant during the y integration. For the y moment, first integrate y over [0,1]. Keep these two different inner calculations separate.\n\nExercise: prove the statement below."


/-- Compute mass and a normalized first moment. -/
Statement exercise_DoubleIntegralValley_5 : (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..1, (1:ℝ)) = 2 ∧ (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..1, x) / 2 = 1 ∧ (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..1, y) / 2 = 1/2 := by
  Hint "1. Calculate the mass, x moment, and y moment separately."
  Hint (hidden := true) "2. Use a pointwise inner-integral formula for the x moment."
  Hint (hidden := true) "3. Use `integral_id` for each variable moment, then divide by the positive mass."
  constructor
  · norm_num [constant_integral]
  · constructor
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..1, x) = x := by
        rw [constant_integral]
        ring
      rw [integral_values innerValue, integral_id]
      norm_num
    · have innerValue : (∫ y : ℝ in 0..1, y) = 1/2 := by
        rw [integral_id]
        norm_num
      rw [innerValue, constant_integral]
      norm_num

Conclusion "Positive mass 2 and the two moments give centroid (1,1/2)."
