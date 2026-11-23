import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 4
Title "A scalar surface integral"

Introduction "Objective: Integrate a scalar density with the area factor.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration. Earlier levels of Surface Expedition.\n\nA scalar surface integral multiplies the scalar density at the surface point by the area factor. Here the density is u and the factor is 1. Name the normal, evaluate the inner integral as u, and integrate it over [0,1]. The increasing parameter bounds give nonnegative area weighting.\n\nExercise: prove the statement below."

/-- Integrate scalar density on a parametrized surface, multiplied by the Euclidean length of its parameter normal. -/
DefinitionDoc VectorCalculus.surfaceIntegral as "surfaceIntegral" in "Calculus notation"
NewDefinition VectorCalculus.surfaceIntegral

/-- Integrate a scalar density with the area factor. -/
Statement exercise_SurfaceExpedition_4 : surfaceIntegral (fun p => p 0) patch 0 1 0 1 = 1/2 := by
  Hint "1. Calculate the parameter normal and hence its length."
  Hint (hidden := true) "2. Prove the inner scalar integral equals u."
  Hint (hidden := true) "3. Replace it under the outer integral and integrate u."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have innerValue (u : ℝ) : (∫ v : ℝ in 0..1, (fun p : Vec => p 0) (patch u v) * length (surfaceNormal patch u v)) = u := by
    norm_num [normal, patch, length, lengthSq, dot, constant_integral]
  rw [surfaceIntegral, integral_values innerValue, integral_id]
  norm_num

Conclusion "The scalar surface integral of the first coordinate equals 1/2."
