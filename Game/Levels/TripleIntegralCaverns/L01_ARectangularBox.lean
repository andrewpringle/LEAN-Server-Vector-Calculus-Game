import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 1
Title "A rectangular box"

Introduction "Objective: Evaluate a triple iterated integral on a box.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments.\n\nEvaluate a triple integral from the innermost variable outward. The z integral is 4; integrating that value over the y interval gives 12; the final x interval doubles it. The box has ordered bounds and continuous constant density. This is the three-variable version of the rectangle method.\n\nWorked example: A box with side lengths 2, 2, and 3 has constant-density integral 3, then 6, then 12 when integrated from the innermost variable outward.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Evaluate a triple iterated integral on a box. -/
Statement exercise_TripleIntegralCaverns_1 : (∫ x : ℝ in 0..2, ∫ y : ℝ in 0..3, ∫ z : ℝ in 0..4, (1:ℝ)) = 24 := by
  Hint "1. Name the z integral first."
  Hint (hidden := true) "2. Name the y integral of the resulting constant."
  Hint (hidden := true) "3. Substitute both values and finish the x integral."
  have innerValue : (∫ z : ℝ in 0..4, (1:ℝ)) = 4 := by
    rw [constant_integral]
    norm_num
  have middle : (∫ y : ℝ in 0..3, (4:ℝ)) = 12 := by
    rw [constant_integral]
    norm_num
  rw [innerValue, middle, constant_integral]
  norm_num

Conclusion "The constant-density box integral equals its volume 24."
