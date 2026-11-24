import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 1
Title "A rectangle"

Introduction "Objective: Evaluate an iterated integral on a rectangle.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments.\n\nIn an iterated integral, evaluate the innermost variable first. Here integrating 1 with respect to y on [0,3] gives 3. Name that result, substitute it into the x integral, and integrate the remaining constant on [0,2]. All bounds are ordered and the integrands are continuous. The result is the rectangle area.\n\nWorked example: On [0,4]×[0,2], first ∫₀²1 dy=2, then ∫₀⁴2 dx=8. Name the inner value and rewrite it in the outer integral.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Evaluate an iterated integral on a rectangle.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..3, (1 : ℝ) = (2 : ℝ) * 6 := by
  have established := exercise_DoubleIntegralValley_1
  rw [established]
``` -/
TheoremDoc exercise_DoubleIntegralValley_1 as "exercise_DoubleIntegralValley_1" in "[anonymous]"

/-- Evaluate an iterated integral on a rectangle. -/
Statement exercise_DoubleIntegralValley_1 : (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..3, (1:ℝ)) = 6 := by
  Hint "1. Name the inner integral and calculate it with `constant_integral`."
  Hint (hidden := true) "2. Rewrite the double integral using that named value."
  Hint (hidden := true) "3. Integrate the resulting constant 3 on [0,2]."
  have innerValue : (∫ y : ℝ in 0..3, (1:ℝ)) = 3 := by
    rw [constant_integral]
    norm_num
  rw [innerValue, constant_integral]
  norm_num

Conclusion "The iterated constant integral gives rectangle area 6."
