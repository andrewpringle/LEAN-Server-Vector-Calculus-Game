import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 6
Title "Boss: the helix"

Introduction "Objective: Combine endpoints, velocity, and speed for a spatial curve.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration. Earlier levels of Curve Navigator.\n\nThe helix adds uniform vertical motion to a circle. Assemble its initial point, velocity at any parameter, and squared speed. The familiar identity sin²t+cos²t=1 supplies the final calculation. Use the existing linear-arithmetic tool to combine that identity with the additional vertical contribution 1.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- The trigonometric identity sin(t)^2 + cos(t)^2 = 1.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x : ℝ), (2 : ℝ) * (Real.sin x ^ 2 + Real.cos x ^ 2) = (2 : ℝ) * 1 := by
  intro x
  have established := Real.sin_sq_add_cos_sq x
  rw [established]
``` -/
TheoremDoc Real.sin_sq_add_cos_sq as "sin_sq_add_cos_sq" in "Calculus"
NewTheorem Real.sin_sq_add_cos_sq
/-- The spatial curve t ↦ (cos t, sin t, t), combining circular motion with uniform vertical motion. -/
DefinitionDoc VectorCalculus.helix as "helix" in "Calculus notation"
NewDefinition VectorCalculus.helix

/-- Combine endpoints, velocity, and speed for a spatial curve.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : 2 * lengthSq (velocity helix t) = 4 := by
  rw [(exercise_CurveNavigator_6 t).2.2]
  norm_num
``` -/
TheoremDoc exercise_CurveNavigator_6 as "exercise_CurveNavigator_6" in "[anonymous]"

/-- Combine endpoints, velocity, and speed for a spatial curve. -/
Statement exercise_CurveNavigator_6 (t : ℝ) : helix 0 = (![1,0,0] : Vec) ∧ velocity helix t = (![-Real.sin t, Real.cos t, 1] : Vec) ∧ lengthSq (velocity helix t) = 2 := by
  Hint "1. Name the velocity formula using component derivatives."
  Hint (hidden := true) "2. Check the initial point and reuse the velocity formula."
  Hint (hidden := true) "3. Expand squared length and combine the sine-cosine identity with the vertical component."
  have vel (s : ℝ) : velocity helix s = (![-Real.sin s,Real.cos s,1] : Vec) := by
    have coordinates (t : ℝ) : helix t = (![Real.cos t,Real.sin t,t] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  constructor
  · apply vector_eq
    · norm_num [helix]
    · norm_num [helix]
    · norm_num [helix]
  · constructor
    · exact vel t
    · rw [vel t]
      norm_num [lengthSq, dot]
      linarith [Real.sin_sq_add_cos_sq t]

Conclusion "The helix has the stated starting point and velocity, with squared speed 2 everywhere."
