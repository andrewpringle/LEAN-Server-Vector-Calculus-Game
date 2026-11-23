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

/-- The trigonometric identity sin(t)^2 + cos(t)^2 = 1. -/
TheoremDoc Real.sin_sq_add_cos_sq as "sin_sq_add_cos_sq" in "Calculus"
NewTheorem Real.sin_sq_add_cos_sq
/-- The spatial curve t ↦ (cos t, sin t, t), combining circular motion with uniform vertical motion. -/
DefinitionDoc VectorCalculus.helix as "helix" in "Calculus notation"
NewDefinition VectorCalculus.helix

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
