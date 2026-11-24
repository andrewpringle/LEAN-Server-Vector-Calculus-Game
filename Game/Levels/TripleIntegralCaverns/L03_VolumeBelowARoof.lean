import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 3
Title "Volume below a roof"

Introduction "Objective: Calculate volume using a variable upper bound.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments. Earlier levels of Triple Integral Caverns.\n\nIntegrate 1 over the sloping-roof solid. Its vertical section has height x. The unit y width leaves that section value unchanged, so the outer integral is ∫₀¹x dx. Prove the inner and middle formulas before evaluating the remaining one-variable integral.\n\nExercise: prove the statement below."


/-- Calculate volume using a variable upper bound.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, ∫ (z : ℝ) in 0..x, (1 : ℝ) = (2 : ℝ) * (1 / 2) := by
  have established := exercise_TripleIntegralCaverns_3
  rw [established]
``` -/
TheoremDoc exercise_TripleIntegralCaverns_3 as "exercise_TripleIntegralCaverns_3" in "[anonymous]"

/-- Calculate volume using a variable upper bound. -/
Statement exercise_TripleIntegralCaverns_3 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..x, (1:ℝ)) = 1/2 := by
  Hint "1. Calculate the vertical integral as x."
  Hint (hidden := true) "2. Calculate the unit-width y integral of that value."
  Hint (hidden := true) "3. Use `integral_values` and `integral_id` for the last integration."
  have innerValue (x : ℝ) : (∫ z : ℝ in 0..x, (1:ℝ)) = x := by
    rw [constant_integral]
    ring
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..x, (1:ℝ)) = x := by
    rw [innerValue, constant_integral]
    ring
  rw [integral_values crossSection, integral_id]
  norm_num

Conclusion "The solid’s volume is 1/2."
