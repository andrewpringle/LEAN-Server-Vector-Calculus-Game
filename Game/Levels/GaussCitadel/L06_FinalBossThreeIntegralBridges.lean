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

/-- The partial derivatives of a scaled coordinate.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (a : ℝ) (j : Fin 3) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => a * q j) p i = (2 : ℝ) * if i = j then a else 0 := by
  intro a j p i
  have established := partial_scaled_coordinate a j p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_scaled_coordinate as "partial_scaled_coordinate" in "Calculus"
/-- Reassembling a vector from its three components recovers that vector.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) • (![p 0, p 1, p 2] : Vec) = (2 : ℝ) • p := by
  intro p
  have established := vector_components p
  rw [established]
``` -/
TheoremDoc VectorCalculus.vector_components as "vector_components" in "Calculus"
/-- Multiplying by one leaves a value unchanged. Here it simplifies the three unit coefficients of the radial field.

### Worked usage example

Remove a unit coefficient in a new scalar expression.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) : 1 * (x + 4) = x + 4 := by
  exact one_mul (x + 4)
``` -/
TheoremDoc one_mul as "one_mul" in "Calculus"
NewTheorem VectorCalculus.partial_scaled_coordinate VectorCalculus.vector_components one_mul

/-- Combine justified special cases of Green, Stokes, and Gauss.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) =
  (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 := by
  have established := exercise_GaussCitadel_6.left
  rw [established]
``` -/
TheoremDoc exercise_GaussCitadel_6 as "exercise_GaussCitadel_6" in "[anonymous]"

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
