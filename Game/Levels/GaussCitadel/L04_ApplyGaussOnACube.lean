import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 4
Title "Apply Gauss on a cube"

Introduction "Objective: Apply a proved divergence-theorem family with verified orientation.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Earlier levels of Gauss Citadel.\n\nApply the proved divergence-theorem family for F=(ax,by,cz) on the outward unit cube. The specified field has coefficients 2, 3, and 4. Smoothness, the bounded solid, and six face orientations are built into this verified special case. The theorem does not assert a result for arbitrary closed surfaces.\n\nExercise: prove the statement below."

/-- Gauss' identity for diagonal linear fields on the outward unit cube.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (a b c : ℝ),
  ((2 : ℝ) * cubeFlux fun p => (![a * p 0, b * p 1, c * p 2] : Vec)) =
    2 *
      ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1,
        divergence (fun p => (![a * p 0, b * p 1, c * p 2] : Vec)) (![x, y, z] : Vec) := by
  intro a b c
  have established := gauss_diagonal a b c
  rw [established]
``` -/
TheoremDoc VectorCalculus.gauss_diagonal as "gauss_diagonal" in "Calculus"
NewTheorem VectorCalculus.gauss_diagonal

/-- Apply a proved divergence-theorem family with verified orientation.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ((2 : ℝ) * cubeFlux fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) =
  2 *
    ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, divergence (fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) (![x, y, z] : Vec) := by
  have established := exercise_GaussCitadel_4
  rw [established]
``` -/
TheoremDoc exercise_GaussCitadel_4 as "exercise_GaussCitadel_4" in "[anonymous]"

/-- Apply a proved divergence-theorem family with verified orientation. -/
Statement exercise_GaussCitadel_4 : cubeFlux (fun p => ![2*p 0,3*p 1,4*p 2]) = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence (fun p => ![2*p 0,3*p 1,4*p 2]) ![x,y,z] := by
  Hint "1. Recognize the diagonal linear field."
  Hint (hidden := true) "2. Identify coefficients 2, 3, and 4 and the outward cube boundary."
  Hint (hidden := true) "3. Apply `gauss_diagonal`."
  apply gauss_diagonal

Conclusion "The proved diagonal-field Gauss identity applies to the outward unit cube."
