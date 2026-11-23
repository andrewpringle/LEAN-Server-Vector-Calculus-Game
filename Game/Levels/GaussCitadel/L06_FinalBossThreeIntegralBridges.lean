import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 6
Title "Final boss: three integral bridges"

Introduction "Objective: Combine justified special cases of Green, Stokes, and Gauss.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Earlier levels of Gauss Citadel.\n\nCombine three established integral bridges. Use the shear Green and Stokes identities on the positive square and upward patch. Use the diagonal Gauss family on the outward cube, noting that coefficients (1,1,1) reconstruct the radial field. Evaluate circulation 2 and flux 3 through their interior integrals, then add them. All three applications are justified proved special cases; the final boss introduces no new tactic.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- The partial derivatives of a scaled coordinate. -/
TheoremDoc VectorCalculus.partial_scaled_coordinate as "partial_scaled_coordinate" in "Calculus"
/-- Reassembling a vector from its three components recovers that vector. -/
TheoremDoc VectorCalculus.vector_components as "vector_components" in "Calculus"
/-- Multiplying by one leaves a value unchanged. Here it simplifies the three unit coefficients of the radial field. -/
TheoremDoc one_mul as "one_mul" in "Calculus"
NewTheorem VectorCalculus.partial_scaled_coordinate VectorCalculus.vector_components one_mul

/-- Combine justified special cases of Green, Stokes, and Gauss. -/
Statement exercise_GaussCitadel_6 : (squareCirculation (fun p => ![0,2*p 0,0]) = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, (curl (fun p => ![0,2*p 0,0]) ![x,y,0]) 2) ∧ (squareCirculation (fun p => ![0,2*p 0,0]) = surfaceFlux (curl (fun p => ![0,2*p 0,0])) patch 0 1 0 1) ∧ (cubeFlux radial = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence radial ![x,y,z]) ∧ squareCirculation (fun p => ![0,2*p 0,0]) + cubeFlux radial = 5 := by
  Hint "1. Identify the Green, Stokes, and Gauss families and their orientations."
  Hint (hidden := true) "2. For Gauss, instantiate coefficients 1,1,1 and use `vector_components` to reconstruct the radial field."
  Hint (hidden := true) "3. Evaluate the two interior integrals, then combine their values."
  have gauss : cubeFlux radial = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence radial ![x,y,z] := by
    have rule := gauss_diagonal 1 1 1
    simp only [one_mul, vector_components] at rule
    exact rule
  constructor
  · apply green_shear
  · constructor
    · apply stokes_shear_patch
    · constructor
      · exact gauss
      · have circulation : squareCirculation (fun p => ![0,2*p 0,0]) = 2 := by
          rw [green_shear]
          norm_num [curl, partial_scaled_coordinate, partial_constant]
        have flux : cubeFlux radial = 3 := by
          rw [gauss]
          norm_num [divergence, radial, partial_coordinate]
        rw [circulation, flux]
        norm_num

Conclusion "The verified Green, Stokes, and Gauss bridges give circulation 2 and flux 3, with combined value 5."
