import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 2
Title "Divergence in the solid"

Introduction "Objective: Integrate a field divergence over the cube.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Earlier levels of Gauss Citadel.\n\nFor the smooth radial field, the three matching coordinate partials give divergence 3. Establish that formula at an arbitrary point before evaluating its triple integral. The unit cube has unit volume, so integrating this constant gives 3. This is the volume side of the divergence identity.\n\nWorked example: For F=(2x,2y,2z), divergence is 6. On a unit cube its volume integral is 6 times volume 1.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Integrate a field divergence over the cube. -/
Statement exercise_GaussCitadel_2 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence radial ![x,y,z]) = 3 := by
  Hint "1. Name the divergence formula for an arbitrary point."
  Hint (hidden := true) "2. Compute its three matching-coordinate partials."
  Hint (hidden := true) "3. Integrate the resulting constant over the unit cube."
  have div (p : Vec) : divergence radial p = 3 := by
    rw [divergence]
    norm_num [radial, partial_coordinate]
  norm_num [div, constant_integral]

Conclusion "The unit-cube divergence volume integral equals 3."
