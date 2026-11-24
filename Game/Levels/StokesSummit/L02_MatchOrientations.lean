import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 2
Title "Match orientations"

Introduction "Objective: Verify the normal and oriented top boundary agree.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Earlier levels of Stokes Summit.\n\nThe upward parameter normal matches a counterclockwise boundary by the right-hand rule. Along the top edge, the tangent must point in the negative x direction. Verify both the surface normal and this oriented boundary tangent; matching a set of boundary points alone would not determine orientation.\n\nWorked example: A downward normal matches clockwise boundary motion when viewed from above. Reversing both orientations preserves the Stokes sign relation.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Verify the normal and oriented top boundary agree.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (t : ℝ), (2 : ℝ) • surfaceNormal patch 0 0 = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  intro t
  have established := (exercise_StokesSummit_2 t).left
  rw [established]
``` -/
TheoremDoc exercise_StokesSummit_2 as "exercise_StokesSummit_2" in "[anonymous]"

/-- Verify the normal and oriented top boundary agree. -/
Statement exercise_StokesSummit_2 (t : ℝ) : surfaceNormal patch 0 0 = (![0,0,1] : Vec) ∧ velocity (fun s => patch (1-s) 1) t = (![-1,0,0] : Vec) := by
  Hint "1. Calculate the upward surface normal."
  Hint (hidden := true) "2. Differentiate the top-edge parametrization with its decreasing first coordinate."
  Hint (hidden := true) "3. Check that its tangent is (-1,0,0)."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  constructor
  · exact normal 0 0
  · simp only [patch, velocity_components]
    apply vector_eq
    · norm_num [deriv_const_sub_id]
    · norm_num [deriv_const_sub_id]
    · norm_num [deriv_const_sub_id]

Conclusion "The upward normal matches the negative-x tangent on the top boundary edge."
