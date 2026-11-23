import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 5
Title "A first moment"

Introduction "Objective: Integrate position times density.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments. Earlier levels of Triple Integral Caverns.\n\nThe x first moment multiplies density x² by position x. After the y and z integrations, use algebra to express the section as x³, then apply the power integral. This distinguishes mass from the moment used in a center-of-mass numerator.\n\nExercise: prove the statement below."


/-- Integrate position times density. -/
Statement exercise_TripleIntegralCaverns_5 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x*x^2) = 1/4 := by
  Hint "1. Multiply position by density before integrating."
  Hint (hidden := true) "2. Prove that the section integral is x³ using constant integrals and `ring`."
  Hint (hidden := true) "3. Substitute that formula and integrate the cube."
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x*x^2) = x^3 := by
    rw [constant_integral, constant_integral]
    ring
  rw [integral_values crossSection, integral_pow]
  norm_num

Conclusion "The x first moment for density x² is 1/4."
