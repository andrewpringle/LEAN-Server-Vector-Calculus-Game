import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 5
Title "Oriented flux"

Introduction "Objective: Integrate a vector field against an oriented area vector.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration. Earlier levels of Surface Expedition.\n\nFlux of the upward unit field through this upward-oriented patch uses the dot product with the unnormalized parameter normal. Its integrand is 1. Calculate that oriented integrand before integrating; no additional area-factor multiplication is needed.\n\nExercise: prove the statement below."

/-- Integrate the field dotted with the parameter cross-product normal. The normal already includes the oriented area factor. -/
DefinitionDoc VectorCalculus.surfaceFlux as "surfaceFlux" in "Calculus notation"
NewDefinition VectorCalculus.surfaceFlux

/-- Integrate a vector field against an oriented area vector.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * surfaceFlux (fun x => (![0, 0, 1] : Vec)) patch 0 1 0 1 = (2 : ℝ) * 1 := by
  have established := exercise_SurfaceExpedition_5
  rw [established]
``` -/
TheoremDoc exercise_SurfaceExpedition_5 as "exercise_SurfaceExpedition_5" in "[anonymous]"

/-- Integrate a vector field against an oriented area vector. -/
Statement exercise_SurfaceExpedition_5 : surfaceFlux (fun _ => ![0,0,1]) patch 0 1 0 1 = 1 := by
  Hint "1. Reuse the upward parameter normal."
  Hint (hidden := true) "2. Calculate the inner integral of the field-normal dot product."
  Hint (hidden := true) "3. Replace it and evaluate the outer constant integral."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have innerValue (u : ℝ) : (∫ v : ℝ in 0..1, dot (![0,0,1] : Vec) (surfaceNormal patch u v)) = 1 := by
    norm_num [normal, dot, constant_integral]
  rw [surfaceFlux, integral_values innerValue, constant_integral]
  norm_num

Conclusion "The upward unit field has flux 1 through the upward patch."
