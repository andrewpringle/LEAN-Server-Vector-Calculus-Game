import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 2
Title "Tangents and normal"

Introduction "Objective: Compute the two parameter tangents and their oriented cross product.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration. Earlier levels of Surface Expedition.\n\nDifferentiate the surface while holding v fixed, then while holding u fixed. These are the two tangent vectors. Their cross product in the stated order is the oriented normal, including the area factor. Name both tangent calculations and reuse them in `surfaceNormal`.\n\nWorked example: For s(u,v)=(2u,v,0), parameter tangents are (2,0,0) and (0,1,0), so the oriented area vector is (0,0,2).\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Differentiate in the first parameter, differentiate in the second, then take their cross product in that order. -/
DefinitionDoc VectorCalculus.surfaceNormal as "surfaceNormal" in "Calculus notation"
NewDefinition VectorCalculus.surfaceNormal

/-- Compute the two parameter tangents and their oriented cross product. -/
Statement exercise_SurfaceExpedition_2 (u v : ℝ) : velocity (fun t => patch t v) u = (![1,0,0] : Vec) ∧ velocity (patch u) v = (![0,1,0] : Vec) ∧ surfaceNormal patch u v = (![0,0,1] : Vec) := by
  Hint "1. Name the derivative in each parameter direction."
  Hint (hidden := true) "2. Use `velocity_components` for each scalar component."
  Hint (hidden := true) "3. Rewrite `surfaceNormal` with the two tangent values and calculate their cross product."
  have du : velocity (fun t => patch t v) u = (![1,0,0] : Vec) := by
    simp only [patch, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  have dv : velocity (patch u) v = (![0,1,0] : Vec) := by
    have coordinates (t : ℝ) : patch u t = (![u,t,0] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  constructor
  · exact du
  · constructor
    · exact dv
    · rw [surfaceNormal, du, dv]
      apply vector_eq
      · norm_num [cross]
      · norm_num [cross]
      · norm_num [cross]

Conclusion "The parameter tangents give the upward oriented normal (0,0,1)."
