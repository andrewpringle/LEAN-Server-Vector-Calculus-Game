import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 3
Title "Area factor"

Introduction "Objective: Compute the Euclidean surface-area density.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration. Earlier levels of Surface Expedition.\n\nThe surface-area factor is the Euclidean length of the parameter normal. The general rule `normal_components` computes that normal from the two parameter derivatives. For this patch its value is (0,0,1), so its length is 1. Scalar area uses the length, while flux retains the orientation vector. A named coordinate formula is passed to `normal_congr` to replace the surface before computing its derivative columns.\n\nExercise: prove the statement below."

/-- The derivative columns give the oriented parameter normal. -/
TheoremDoc VectorCalculus.normal_components as "normal_components" in "Calculus"
/-- Replacing a surface by a pointwise equal parametrization preserves its two derivative tangents and oriented parameter normal. -/
TheoremDoc VectorCalculus.normal_congr as "normal_congr" in "Calculus"
NewTheorem VectorCalculus.normal_components VectorCalculus.normal_congr

/-- Compute the Euclidean surface-area density. -/
Statement exercise_SurfaceExpedition_3 (u v : ℝ) : length (surfaceNormal patch u v) = 1 := by
  Hint "1. Compute the normal from the two parameter derivative columns."
  Hint (hidden := true) "2. Substitute the normal into the length."
  Hint (hidden := true) "3. Evaluate its squared Euclidean length and square root."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  rw [normal]
  norm_num [length, lengthSq, dot]

Conclusion "The parameter normal has Euclidean length 1, the required scalar area factor."
