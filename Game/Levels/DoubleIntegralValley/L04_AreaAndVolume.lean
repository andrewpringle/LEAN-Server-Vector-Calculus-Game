import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 4
Title "Area and volume"

Introduction "Objective: Compute area and the volume below a constant roof.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments. Earlier levels of Double Integral Valley.\n\nIntegrating 1 gives the rectangle area; integrating the nonnegative height 4 gives the volume below a constant roof. Calculate the inner constant integral and then the outer one in each case. The same bounds describe the two applications.\n\nExercise: prove the statement below."


/-- Compute area and the volume below a constant roof. -/
Statement exercise_DoubleIntegralValley_4 : (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..3, (1:ℝ)) = 6 ∧ (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..3, (4:ℝ)) = 24 := by
  Hint "1. Separate area and volume."
  Hint (hidden := true) "2. Apply `constant_integral` twice in each part."
  Hint (hidden := true) "3. Evaluate the side lengths and the height."
  constructor
  · rw [constant_integral, constant_integral]
    norm_num
  · rw [constant_integral, constant_integral]
    norm_num

Conclusion "The rectangle has area 6 and volume 24 below height 4."
