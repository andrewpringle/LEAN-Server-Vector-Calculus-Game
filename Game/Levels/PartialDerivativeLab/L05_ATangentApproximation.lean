import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 5
Title "A tangent approximation"

Introduction "Objective: Construct the affine approximation and bound its exact error.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals. Earlier levels of Partial Derivative Lab.\n\nAt (1,1), the linear approximation to x²+y² is 2+2h+2k. Subtract it from the exact value at (1+h,1+k). The remaining h²+k² measures the approximation error and has no constant or linear terms. The polynomial tool introduced earlier now verifies this identity.\n\nExercise: prove the statement below."


/-- Construct the affine approximation and bound its exact error.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (h k : ℝ), (2 : ℝ) * ((1 + h) ^ 2 + (1 + k) ^ 2 - (2 + (2 : ℝ) * h + (2 : ℝ) * k)) = (2 : ℝ) * (h ^ 2 + k ^ 2) := by
  intro h k
  have established := exercise_PartialDerivativeLab_5 h k
  rw [established]
``` -/
TheoremDoc exercise_PartialDerivativeLab_5 as "exercise_PartialDerivativeLab_5" in "[anonymous]"

/-- Construct the affine approximation and bound its exact error. -/
Statement exercise_PartialDerivativeLab_5 (h k : ℝ) : (1+h)^2 + (1+k)^2 - (2 + 2*h + 2*k) = h^2+k^2 := by
  Hint "1. Expand around (1,1) using displacements h and k."
  Hint (hidden := true) "2. Remove the value and the two linear terms."
  Hint (hidden := true) "3. Use `ring` to verify that only h²+k² remains."
  ring

Conclusion "The linear approximation leaves exactly the quadratic error h²+k²."
