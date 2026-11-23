import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 6
Title "Boss: reverse the patch"

Introduction "Objective: Compare equal scalar area and opposite oriented flux.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration. Earlier levels of Surface Expedition.\n\nInterchanging the parameter order reverses the normal while preserving its length. Calculate both normals, the two fluxes, and the two scalar areas. Then compare the results. This distinguishes orientation-sensitive flux from orientation-independent area by a fully checked concrete example.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Compare equal scalar area and opposite oriented flux. -/
Statement exercise_SurfaceExpedition_6 : surfaceFlux (fun _ => ![0,0,1]) (fun u v => ![v,u,0]) 0 1 0 1 = -surfaceFlux (fun _ => ![0,0,1]) patch 0 1 0 1 ∧ surfaceIntegral (fun _ => 1) (fun u v => ![v,u,0]) 0 1 0 1 = surfaceIntegral (fun _ => 1) patch 0 1 0 1 := by
  Hint "1. Calculate the original and reversed parameter normals."
  Hint (hidden := true) "2. Use those normals to name the two fluxes and the two areas."
  Hint (hidden := true) "3. Substitute the four values into the requested comparisons."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have reversed (u v : ℝ) : surfaceNormal (fun s t => ![t,s,0]) u v = (![0,0,-1] : Vec) := by
    rw [normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have upFlux : surfaceFlux (fun _ => ![0,0,1]) patch 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, normal, dot]
  have downFlux : surfaceFlux (fun _ => ![0,0,1]) (fun u v => ![v,u,0]) 0 1 0 1 = -1 := by
    norm_num [surfaceFlux, reversed, dot]
  have upArea : surfaceIntegral (fun _ => 1) patch 0 1 0 1 = 1 := by
    norm_num [surfaceIntegral, normal, length, lengthSq, dot]
  have downArea : surfaceIntegral (fun _ => 1) (fun u v => ![v,u,0]) 0 1 0 1 = 1 := by
    norm_num [surfaceIntegral, reversed, length, lengthSq, dot]
  constructor
  · rw [downFlux, upFlux]
  · rw [downArea, upArea]

Conclusion "Parameter reversal negates flux while preserving scalar surface area."
