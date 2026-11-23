import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 6
Title "Boss: an absolute Jacobian"

Introduction "Objective: Verify a change-of-variables equality with an orientation-reversing map.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities. Earlier levels of Coordinate Portal.\n\nThe orientation-reversing map sends the unit square to [0,2]×[-3,0]. Compare the original constant-density integral with the transformed one using the absolute determinant 6. Calculate the rectangle integral and determinant independently, then combine them. This verifies the stated change-of-variables special case by direct integration.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Verify a change-of-variables equality with an orientation-reversing map. -/
Statement exercise_CoordinatePortal_6 : (∫ x : ℝ in 0..2, ∫ y : ℝ in (-3)..0, (1:ℝ)) = (∫ u : ℝ in 0..1, ∫ v : ℝ in 0..1, |Matrix.det (!![(2:ℝ),0;0,-3])|) := by
  Hint "1. Compute the absolute determinant, retaining its positive sign."
  Hint (hidden := true) "2. Evaluate the original rectangle integral."
  Hint (hidden := true) "3. Substitute both values and check the transformed unit-square integral."
  have determinant : |Matrix.det (!![(2:ℝ),0;0,-3])| = 6 := by
    norm_num [Matrix.det_fin_two]
  have original : (∫ x : ℝ in 0..2, ∫ y : ℝ in (-3)..0, (1:ℝ)) = 6 := by
    norm_num [constant_integral]
  rw [original, determinant]
  norm_num [constant_integral]

Conclusion "The two directly evaluated integrals agree using the absolute determinant, verifying the stated substitution special case."
