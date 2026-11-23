import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 5
Title "Apply Stokes: square patch"

Introduction "Objective: Apply an established Stokes special-case family.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Earlier levels of Stokes Summit.\n\nApply the proved Stokes special case for a shear field on the upward unit-square patch. The boundary is the counterclockwise square established earlier, and the field is smooth. `stokes_shear_patch` packages this verified family; it is not a general arbitrary-surface theorem.\n\nExercise: prove the statement below."

/-- Stokes' identity for a linear shear on an upward unit-square patch. -/
TheoremDoc VectorCalculus.stokes_shear_patch as "stokes_shear_patch" in "Calculus"
NewTheorem VectorCalculus.stokes_shear_patch

/-- Apply an established Stokes special-case family. -/
Statement exercise_StokesSummit_5 : squareCirculation (fun p => ![0,2*p 0,0]) = surfaceFlux (curl (fun p => ![0,2*p 0,0])) patch 0 1 0 1 := by
  Hint "1. Recognize coefficient 2 in the shear field."
  Hint (hidden := true) "2. Check that the boundary and patch orientations match the proved family."
  Hint (hidden := true) "3. Apply `stokes_shear_patch`."
  apply stokes_shear_patch

Conclusion "The proved shear-family Stokes identity applies to the upward square patch."
