import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 4
Title "Variable density"

Introduction "Objective: Compute mass from a nonconstant density.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments. Earlier levels of Triple Integral Caverns.\n\nThe density x² is nonnegative on the unit cube and varies with x. Treat it as constant while integrating over y and z. The section integral remains x²; only then apply the power integration rule in x. Vanishing density on one face does not make the total mass zero.\n\nExercise: prove the statement below."


/-- Compute mass from a nonconstant density.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, x ^ 2 = (2 : ℝ) * (1 / 3) := by
  have established := exercise_TripleIntegralCaverns_4
  rw [established]
``` -/
TheoremDoc exercise_TripleIntegralCaverns_4 as "exercise_TripleIntegralCaverns_4" in "[anonymous]"

/-- Compute mass from a nonconstant density. -/
Statement exercise_TripleIntegralCaverns_4 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x^2) = 1/3 := by
  Hint "1. Name the two-variable section integral for a fixed x."
  Hint (hidden := true) "2. Use the two unit side lengths to simplify that section."
  Hint (hidden := true) "3. Replace the section and apply `integral_pow`."
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x^2) = x^2 := by
    rw [constant_integral, constant_integral]
    ring
  rw [integral_values crossSection, integral_pow]
  norm_num

Conclusion "The unit-cube density x² has positive total mass 1/3."
