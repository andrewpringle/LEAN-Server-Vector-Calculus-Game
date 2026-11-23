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

/-- Display a gradient as its three partial derivatives. -/
TheoremDoc VectorCalculus.gradient_components as "gradient_components" in "Calculus"
/-- The squared-distance field has partial derivative twice the chosen coordinate. -/
TheoremDoc VectorCalculus.partial_sum_squares as "partial_sum_squares" in "Calculus"
NewTheorem VectorCalculus.gradient_components VectorCalculus.partial_sum_squares
/-- The vector of a scalar field’s three coordinate partial derivatives, in x, y, z order. -/
DefinitionDoc VectorCalculus.gradient as "gradient" in "Calculus notation"
NewDefinition VectorCalculus.gradient

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
