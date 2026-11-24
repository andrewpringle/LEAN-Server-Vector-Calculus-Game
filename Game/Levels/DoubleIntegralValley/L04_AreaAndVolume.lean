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


/-- Compute area and the volume below a constant roof.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..3, (1 : ℝ) = (2 : ℝ) * 6 := by
  have established := exercise_DoubleIntegralValley_4.left
  rw [established]
``` -/
TheoremDoc exercise_DoubleIntegralValley_4 as "exercise_DoubleIntegralValley_4" in "[anonymous]"

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
