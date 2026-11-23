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

/-- The identity matrix has ones on its diagonal and zeros elsewhere. -/
TheoremDoc Matrix.one_apply as "one_apply" in "Calculus"
/-- Entrywise equality for a 3 by 3 Jacobian; indices start at zero. -/
TheoremDoc VectorCalculus.matrix_eq as "matrix_eq" in "Calculus"
NewTheorem Matrix.one_apply VectorCalculus.matrix_eq
/-- Derivative matrix: row i, column j is the j partial of output component i. -/
DefinitionDoc VectorCalculus.jacobian as "jacobian" in "Calculus notation"
NewDefinition VectorCalculus.jacobian

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
