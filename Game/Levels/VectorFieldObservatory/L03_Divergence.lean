import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 3
Title "Divergence"

Introduction "Objective: Compute a field divergence using the appropriate coordinate derivatives.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Earlier levels of Vector Field Observatory.\n\nDivergence adds only the matching-coordinate partials: ∂F₀/∂x₀, ∂F₁/∂x₁, and ∂F₂/∂x₂. For the radial field each is a coordinate derivative equal to 1. Choose those terms using the definition before calculating their sum.\n\nExercise: prove the statement below."

/-- Sum the three matching-coordinate partials of a vector field; cross-coordinate partials do not enter divergence. -/
DefinitionDoc VectorCalculus.divergence as "divergence" in "Calculus notation"
NewDefinition VectorCalculus.divergence

/-- Compute a field divergence using the appropriate coordinate derivatives.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) * divergence radial p = (2 : ℝ) * 3 := by
  intro p
  have established := exercise_VectorFieldObservatory_3 p
  rw [established]
``` -/
TheoremDoc exercise_VectorFieldObservatory_3 as "exercise_VectorFieldObservatory_3" in "[anonymous]"

/-- Compute a field divergence using the appropriate coordinate derivatives. -/
Statement exercise_VectorFieldObservatory_3 (p : Vec) : divergence radial p = 3 := by
  Hint "1. Open the sum in `divergence`."
  Hint (hidden := true) "2. Use the coordinate derivative rule on each matching entry."
  Hint (hidden := true) "3. Add the three ones."
  rw [divergence]
  norm_num [radial, partial_coordinate]

Conclusion "The radial field has divergence 3."
