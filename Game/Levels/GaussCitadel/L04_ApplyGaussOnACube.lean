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

/-- Gauss' identity for diagonal linear fields on the outward unit cube. -/
TheoremDoc VectorCalculus.gauss_diagonal as "gauss_diagonal" in "Calculus"
NewTheorem VectorCalculus.gauss_diagonal

/-- Apply a proved divergence-theorem family with verified orientation. -/
Statement exercise_GaussCitadel_4 : cubeFlux (fun p => ![2*p 0,3*p 1,4*p 2]) = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence (fun p => ![2*p 0,3*p 1,4*p 2]) ![x,y,z] := by
  Hint "1. Recognize the diagonal linear field."
  Hint (hidden := true) "2. Identify coefficients 2, 3, and 4 and the outward cube boundary."
  Hint (hidden := true) "3. Apply `gauss_diagonal`."
  apply gauss_diagonal

Conclusion "The proved diagonal-field Gauss identity applies to the outward unit cube."
