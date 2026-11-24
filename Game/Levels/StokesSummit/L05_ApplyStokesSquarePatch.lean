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

/-- Stokes' identity for a linear shear on an upward unit-square patch.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (k : ℝ),
  ((2 : ℝ) * squareCirculation fun p => (![0, k * p 0, 0] : Vec)) =
    (2 : ℝ) * surfaceFlux (curl fun p => (![0, k * p 0, 0] : Vec)) patch 0 1 0 1 := by
  intro k
  have established := stokes_shear_patch k
  rw [established]
``` -/
TheoremDoc VectorCalculus.stokes_shear_patch as "stokes_shear_patch" in "Calculus"
NewTheorem VectorCalculus.stokes_shear_patch

/-- Apply an established Stokes special-case family.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) =
  (2 : ℝ) * surfaceFlux (curl fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) patch 0 1 0 1 := by
  have established := exercise_StokesSummit_5
  rw [established]
``` -/
TheoremDoc exercise_StokesSummit_5 as "exercise_StokesSummit_5" in "[anonymous]"

/-- Apply an established Stokes special-case family. -/
Statement exercise_StokesSummit_5 : squareCirculation (fun p => ![0,2*p 0,0]) = surfaceFlux (curl (fun p => ![0,2*p 0,0])) patch 0 1 0 1 := by
  Hint "1. Recognize coefficient 2 in the shear field."
  Hint (hidden := true) "2. Check that the boundary and patch orientations match the proved family."
  Hint (hidden := true) "3. Apply `stokes_shear_patch`."
  apply stokes_shear_patch

Conclusion "The proved shear-family Stokes identity applies to the upward square patch."
