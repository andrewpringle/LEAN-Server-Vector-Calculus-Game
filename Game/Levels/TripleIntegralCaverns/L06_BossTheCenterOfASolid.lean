import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 6
Title "Boss: the center of a solid"

Introduction "Objective: Compute positive mass and three normalized moments.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments. Earlier levels of Triple Integral Caverns.\n\nThe uniform unit cube is symmetric, suggesting center (1/2,1/2,1/2). Justify that prediction by computing positive mass 1 and all three coordinate moments. Each moment requires choosing the correct varying variable. Divide by the computed positive mass, rather than using symmetry as an unproved conclusion.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Compute positive mass and three normalized moments.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, (1 : ℝ) = (2 : ℝ) * 1 := by
  have established := exercise_TripleIntegralCaverns_6.left
  rw [established]
``` -/
TheoremDoc exercise_TripleIntegralCaverns_6 as "exercise_TripleIntegralCaverns_6" in "[anonymous]"

/-- Compute positive mass and three normalized moments. -/
Statement exercise_TripleIntegralCaverns_6 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, (1:ℝ)) = 1 ∧ (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x) / 1 = 1/2 ∧ (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, y) / 1 = 1/2 ∧ (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, z) / 1 = 1/2 := by
  Hint "1. Separate mass and the three normalized moments."
  Hint (hidden := true) "2. For each moment, identify which integration first involves a varying coordinate."
  Hint (hidden := true) "3. Use the constant and identity integral rules, then divide by mass 1."
  constructor
  · norm_num [constant_integral]
  · constructor
    · have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x) = x := by
        rw [constant_integral, constant_integral]
        ring
      rw [integral_values crossSection, integral_id]
      norm_num
    · constructor
      · have innerValue (y : ℝ) : (∫ z : ℝ in 0..1, y) = y := by
          rw [constant_integral]
          ring
        have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, y) = 1/2 := by
          rw [integral_values innerValue, integral_id]
          norm_num
        rw [integral_values crossSection, constant_integral]
        norm_num
      · have innerValue : (∫ z : ℝ in 0..1, z) = 1/2 := by
          rw [integral_id]
          norm_num
        rw [innerValue, constant_integral, constant_integral]
        norm_num

Conclusion "Direct integration verifies the uniform cube’s positive mass and center (1/2,1/2,1/2)."
