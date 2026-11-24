import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 4
Title "A Jacobian matrix"

Introduction "Objective: Compute entries of the derivative matrix of a vector map.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices. Earlier levels of Gradient Mountain.\n\nThe Jacobian entry in row i and column j is the j partial of output component i. For the identity map, matching coordinates give 1 and the other entries give 0. The proved rule `matrix_eq` asks for the nine entries in row order, so no matrix-extensionality tactic is needed.\n\nExercise: prove the statement below."

/-- The identity matrix has ones on its diagonal and zeros elsewhere.

### Worked usage example

The identity matrix has a zero in an off-diagonal position.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 := by
  rw [Matrix.one_apply]
  norm_num
``` -/
TheoremDoc Matrix.one_apply as "one_apply" in "Calculus"
/-- Entrywise equality for a 3 by 3 Jacobian; indices start at zero.

### Worked usage example

Use the equality in the opposite direction. Rewriting works inside a goal, including when the known value is on its left.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {A B : Matrix (Fin 3) (Fin 3) ℝ},
  A 0 0 = B 0 0 →
    A 0 1 = B 0 1 →
      A 0 2 = B 0 2 →
        A 1 0 = B 1 0 →
          A 1 1 = B 1 1 → A 1 2 = B 1 2 → A 2 0 = B 2 0 → A 2 1 = B 2 1 → A 2 2 = B 2 2 → B = A := by
  intro A B h00 h01 h02 h10 h11 h12 h20 h21 h22
  have established := matrix_eq h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [established]
``` -/
TheoremDoc VectorCalculus.matrix_eq as "matrix_eq" in "Calculus"
NewTheorem Matrix.one_apply VectorCalculus.matrix_eq
/-- Derivative matrix: row i, column j is the j partial of output component i. -/
DefinitionDoc VectorCalculus.jacobian as "jacobian" in "Calculus notation"
NewDefinition VectorCalculus.jacobian

/-- Compute entries of the derivative matrix of a vector map.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the completed Jacobian formula to read an off-diagonal entry. Matrix.one_apply evaluates an entry of the identity matrix.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (p : Vec) : (jacobian (fun q => ![q 0,q 1,q 2]) p) 0 2 = 0 := by
  rw [exercise_GradientMountain_4 p]
  norm_num [Matrix.one_apply]
``` -/
TheoremDoc exercise_GradientMountain_4 as "exercise_GradientMountain_4" in "[anonymous]"

/-- Compute entries of the derivative matrix of a vector map. -/
Statement exercise_GradientMountain_4 (p : Vec) : jacobian (fun q => ![q 0,q 1,q 2]) p = (1 : Matrix (Fin 3) (Fin 3) ℝ) := by
  Hint "1. Apply `matrix_eq` to compare the nine entries in row order."
  Hint (hidden := true) "2. Open each entry using `jacobian` and `partial_coordinate`."
  Hint (hidden := true) "3. Compare with the corresponding entry of the identity matrix."
  apply matrix_eq
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]

Conclusion "The identity map has the identity Jacobian matrix."
