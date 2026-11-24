import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 6
Title "Boss: an implicit tangent plane"

Introduction "Objective: Use a regular gradient to identify a tangent plane.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals. Earlier levels of Partial Derivative Lab.\n\nFor the unit sphere at (1,0,0), verify the point lies on the surface, calculate its gradient, prove that gradient is nonzero, and identify its point-normal tangent plane. `gradient_components` displays the three partials; `partial_sum_squares` supplies the squared-coordinate power rule. Regularity is the nonzero-gradient check, which must not be omitted.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Display a gradient as its three partial derivatives.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (f : ScalarField) (p : Vec),
  (2 : ℝ) • gradient f p = (2 : ℝ) • (![coordPartial f p 0, coordPartial f p 1, coordPartial f p 2] : Vec) := by
  intro f p
  have established := gradient_components f p
  rw [established]
``` -/
TheoremDoc VectorCalculus.gradient_components as "gradient_components" in "Calculus"
/-- The squared-distance field has partial derivative twice the chosen coordinate.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec) (i : Fin 3), (2 : ℝ) * coordPartial squarePotential p i = (2 : ℝ) * ((2 : ℝ) * p i) := by
  intro p i
  have established := partial_sum_squares p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_sum_squares as "partial_sum_squares" in "Calculus"
NewTheorem VectorCalculus.gradient_components VectorCalculus.partial_sum_squares
/-- The vector of a scalar field’s three coordinate partial derivatives, in x, y, z order. -/
DefinitionDoc VectorCalculus.gradient as "gradient" in "Calculus notation"
NewDefinition VectorCalculus.gradient

/-- Use a regular gradient to identify a tangent plane.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the completed tangent-plane criterion in the opposite direction: a point with first coordinate one belongs to the tangent plane.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (q : Vec) (h : q 0 = 1) : onPlane ![2,0,0] ![1,0,0] q := by
  apply (exercise_PartialDerivativeLab_6 q).2.2.2.mpr
  exact h
``` -/
TheoremDoc exercise_PartialDerivativeLab_6 as "exercise_PartialDerivativeLab_6" in "[anonymous]"

/-- Use a regular gradient to identify a tangent plane. -/
Statement exercise_PartialDerivativeLab_6 (q : Vec) : squarePotential ![1,0,0] = 1 ∧ gradient squarePotential ![1,0,0] = (![2,0,0] : Vec) ∧ (![2,0,0] : Vec) ≠ 0 ∧ (onPlane ![2,0,0] ![1,0,0] q ↔ q 0 = 1) := by
  Hint "1. Separate surface membership, gradient, nonzero normal, and plane equation."
  Hint (hidden := true) "2. Use the component gradient rule and the partial derivatives of the sum of squares."
  Hint (hidden := true) "3. Use a nonzero component for regularity; solve the point-normal equation as in Space Explorer."
  constructor
  · rw [squarePotential]
    norm_num
  · constructor
    · rw [gradient_components]
      apply vector_eq
      · norm_num [partial_sum_squares]
      · norm_num [partial_sum_squares]
      · norm_num [partial_sum_squares]
    · constructor
      · apply vector_ne_zero 0
        norm_num
      · constructor
        · intro h
          norm_num [onPlane, dot] at h
          linarith
        · intro h
          norm_num [onPlane, dot, h]

Conclusion "The sphere point is regular and its gradient determines the stated tangent plane."
