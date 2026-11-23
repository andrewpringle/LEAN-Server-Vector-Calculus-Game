import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 2
Title "Differentiate a curve"

Introduction "Objective: Compute the component derivatives of a vector curve.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration. Earlier levels of Curve Navigator.\n\nVelocity differentiates the three scalar component functions. The proved rule `velocity_components` displays those three derivatives. `deriv_pow_field` is the ordinary power rule; Lean already knows the derivatives of the identity and constant functions. Apply these rules coordinate by coordinate.\n\nWorked example: For c(t)=(t³,0,0), the component power rule gives velocity (3t²,0,0). Each output coordinate is differentiated separately.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Component derivatives compute the derivative of a parametrized spatial curve. -/
TheoremDoc VectorCalculus.velocity_components as "velocity_components" in "Calculus"
/-- Power rule for the scalar derivative of x raised to a natural-number power. Numeric exponents simplify with norm_num. -/
TheoremDoc deriv_pow_field as "deriv_pow_field" in "Calculus"
NewTheorem VectorCalculus.velocity_components deriv_pow_field
/-- Differentiate the three component functions of a parametrized curve. Use velocity_components to display those derivatives. -/
DefinitionDoc VectorCalculus.velocity as "velocity" in "Calculus notation"
/-- The scalar derivative value deriv f t. The derivative rules in the inventory justify the calculations used here. -/
DefinitionDoc deriv as "deriv" in "Calculus notation"
NewDefinition VectorCalculus.velocity deriv

/-- Compute the component derivatives of a vector curve. -/
Statement exercise_CurveNavigator_2 (t : ℝ) : velocity (fun s => ![s,s^2,0]) t = (![1,2*t,0] : Vec) := by
  Hint "1. Rewrite with `velocity_components`."
  Hint (hidden := true) "2. Use `vector_eq` to compare the three derivative values."
  Hint (hidden := true) "3. Use `norm_num [deriv_pow_field]` for each scalar derivative."
  rw [velocity_components]
  apply vector_eq
  · norm_num [deriv_pow_field]
  · norm_num [deriv_pow_field]
  · norm_num [deriv_pow_field]

Conclusion "Each curve component has the stated derivative."
