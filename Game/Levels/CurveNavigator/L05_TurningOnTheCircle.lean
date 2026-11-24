import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 5
Title "Turning on the circle"

Introduction "Objective: Compute a unit tangent and curvature at a circle point.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration. Earlier levels of Curve Navigator.\n\nOn a regular curve, divide velocity by speed to obtain a unit tangent. Curvature is |v×a|/|v|³. At parameter zero on the unit circle, velocity is (0,1,0), acceleration is (-1,0,0), and speed is 1. Name these ingredients, then substitute them into the two geometric formulas.\n\nExercise: prove the statement below."

/-- The scalar function t ↦ -t has derivative -1 at every real point.

### Worked usage example

This particular lemma differentiates the negation function t ↦ -t.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : deriv (fun s : ℝ => -s) t = -1 := by
  exact deriv_neg t
``` -/
TheoremDoc deriv_neg as "deriv_neg" in "Calculus"
NewTheorem deriv_neg
/-- The real cosine function, with angles in radians. -/
DefinitionDoc Real.cos as "cos" in "Calculus notation"
/-- The real sine function, with angles in radians. -/
DefinitionDoc Real.sin as "sin" in "Calculus notation"
/-- The unit circle parametrization t ↦ (cos t, sin t, 0). Increasing t gives counterclockwise motion. -/
DefinitionDoc VectorCalculus.circle as "circle" in "Calculus notation"
/-- For a regular curve, curvature is the length of velocity cross acceleration divided by speed cubed. -/
DefinitionDoc VectorCalculus.curvature as "curvature" in "Calculus notation"
/-- Divide velocity by its Euclidean speed on a regular curve, where speed is nonzero. -/
DefinitionDoc VectorCalculus.unitTangent as "unitTangent" in "Calculus notation"
NewDefinition Real.cos Real.sin VectorCalculus.circle VectorCalculus.curvature VectorCalculus.unitTangent

/-- Compute a unit tangent and curvature at a circle point.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) • unitTangent circle 0 = (2 : ℝ) • (![0, 1, 0] : Vec) := by
  have established := exercise_CurveNavigator_5.left
  rw [established]
``` -/
TheoremDoc exercise_CurveNavigator_5 as "exercise_CurveNavigator_5" in "[anonymous]"

/-- Compute a unit tangent and curvature at a circle point. -/
Statement exercise_CurveNavigator_5 : unitTangent circle 0 = (![0,1,0] : Vec) ∧ curvature circle 0 = 1 := by
  Hint "1. Name velocity, acceleration at zero, and speed at zero."
  Hint (hidden := true) "2. Substitute those facts into `unitTangent`."
  Hint (hidden := true) "3. Substitute them into `curvature` and compute the cross-product length."
  have vel (s : ℝ) : velocity circle s = (![-Real.sin s,Real.cos s,0] : Vec) := by
    have coordinates (t : ℝ) : circle t = (![Real.cos t,Real.sin t,0] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  have acc : velocity (velocity circle) 0 = (![-1,0,0] : Vec) := by
    rw [velocity_congr vel, velocity_components]
    apply vector_eq
    · norm_num [deriv_neg]
    · norm_num [deriv_neg]
    · norm_num [deriv_neg]
  have sp : speed circle 0 = 1 := by
    rw [speed, vel 0]
    norm_num [length, lengthSq, dot]
  constructor
  · rw [unitTangent, sp, vel 0]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · rw [curvature, sp, vel 0, acc]
    norm_num [length, lengthSq, dot, cross]

Conclusion "The circle has the stated unit tangent and curvature 1 at parameter zero."
