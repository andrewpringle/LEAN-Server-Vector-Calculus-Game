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

/-- Component derivatives compute the derivative of a parametrized spatial curve.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y z : ℝ → ℝ) (t : ℝ),
  (2 : ℝ) • velocity (fun s => (![x s, y s, z s] : Vec)) t = (2 : ℝ) • (![deriv x t, deriv y t, deriv z t] : Vec) := by
  intro x y z t
  have established := velocity_components x y z t
  rw [established]
``` -/
TheoremDoc VectorCalculus.velocity_components as "velocity_components" in "Calculus"
/-- Power rule for the scalar derivative of x raised to a natural-number power. Numeric exponents simplify with norm_num.

### Worked usage example

Differentiate a cube, then simplify its numerical exponent and coefficient.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : deriv (fun s : ℝ => s^3) t = 3*t^2 := by
  rw [deriv_pow_field]
  norm_num
``` -/
TheoremDoc deriv_pow_field as "deriv_pow_field" in "Calculus"
NewTheorem VectorCalculus.velocity_components deriv_pow_field
/-- Differentiate the three component functions of a parametrized curve. Use velocity_components to display those derivatives. -/
DefinitionDoc VectorCalculus.velocity as "velocity" in "Calculus notation"
/-- The scalar derivative value deriv f t. The derivative rules in the inventory justify the calculations used here. -/
DefinitionDoc deriv as "deriv" in "Calculus notation"
NewDefinition VectorCalculus.velocity deriv

/-- Compute the component derivatives of a vector curve.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (t : ℝ), (2 : ℝ) • velocity (fun s => (![s, s ^ 2, 0] : Vec)) t = (2 : ℝ) • (![1, (2 : ℝ) * t, 0] : Vec) := by
  intro t
  have established := exercise_CurveNavigator_2 t
  rw [established]
``` -/
TheoremDoc exercise_CurveNavigator_2 as "exercise_CurveNavigator_2" in "[anonymous]"

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
