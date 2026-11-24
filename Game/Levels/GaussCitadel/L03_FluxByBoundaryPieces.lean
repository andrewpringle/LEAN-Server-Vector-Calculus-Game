import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 3
Title "Flux by boundary pieces"

Introduction "Objective: Compute flux directly on the six outward-oriented faces.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Earlier levels of Gauss Citadel.\n\nCalculate outward flux directly through all six cube faces for the radial field. Each face at coordinate 1 contributes 1; each face at coordinate 0 contributes 0. Name the six actual surface integrals before adding them in `cubeFlux`. This calculation does not use the divergence theorem.\n\nExercise: prove the statement below."

/-- Six square parametrizations whose parameter cross products point outward. -/
DefinitionDoc VectorCalculus.cubeFlux as "cubeFlux" in "Calculus notation"
NewDefinition VectorCalculus.cubeFlux

/-- Compute flux directly on the six outward-oriented faces.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * cubeFlux radial = (2 : ℝ) * 3 := by
  have established := exercise_GaussCitadel_3
  rw [established]
``` -/
TheoremDoc exercise_GaussCitadel_3 as "exercise_GaussCitadel_3" in "[anonymous]"

/-- Compute flux directly on the six outward-oriented faces. -/
Statement exercise_GaussCitadel_3 : cubeFlux radial = 3 := by
  Hint "1. Evaluate one outward-oriented surface integral per face."
  Hint (hidden := true) "2. Use the face normals to distinguish positive and zero contributions."
  Hint (hidden := true) "3. Rewrite the six-face sum with those values and add."
  have face1 : surfaceFlux radial (fun s t => ![1,s,t]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face2 : surfaceFlux radial (fun s t => ![0,t,s]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face3 : surfaceFlux radial (fun s t => ![t,1,s]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face4 : surfaceFlux radial (fun s t => ![s,0,t]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face5 : surfaceFlux radial (fun s t => ![s,t,1]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face6 : surfaceFlux radial (fun s t => ![t,s,0]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  rw [cubeFlux, face1, face2, face3, face4, face5, face6]
  norm_num

Conclusion "Adding six independently computed outward face fluxes gives total flux 3."
