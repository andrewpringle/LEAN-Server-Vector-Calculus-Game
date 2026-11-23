import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 4
Title "Curl"

Introduction "Objective: Compute an oriented curl from coordinate partial derivatives.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Earlier levels of Vector Field Observatory.\n\nCurl uses the right-handed difference of cross-coordinate partials. For (-y/2,x/2,0), the only nonzero component is ∂(x/2)/∂x minus ∂(-y/2)/∂y. The rules `partial_div_const` and `partial_neg` express the familiar constant-factor and sign laws. Compute components without exposing coordinate updates.\n\nExercise: prove the statement below."

/-- A constant scalar field has zero partial derivatives. -/
TheoremDoc VectorCalculus.partial_constant as "partial_constant" in "Calculus"
/-- Division by a fixed scalar commutes with a partial derivative. -/
TheoremDoc VectorCalculus.partial_div_const as "partial_div_const" in "Calculus"
/-- Negating a field negates its partial derivatives. -/
TheoremDoc VectorCalculus.partial_neg as "partial_neg" in "Calculus"
NewTheorem VectorCalculus.partial_constant VectorCalculus.partial_div_const VectorCalculus.partial_neg
/-- Right-handed curl: the three differences of cross-coordinate partial derivatives in cyclic coordinate order. -/
DefinitionDoc VectorCalculus.curl as "curl" in "Calculus notation"
NewDefinition VectorCalculus.curl

/-- Compute an oriented curl from coordinate partial derivatives. -/
Statement exercise_VectorFieldObservatory_4 (p : Vec) : curl rotation p = (![0,0,1] : Vec) := by
  Hint "1. Open `curl` and compare its components."
  Hint (hidden := true) "2. Use the coordinate, constant, negative, and constant-division partial rules."
  Hint (hidden := true) "3. The third component is 1/2 minus -1/2."
  rw [curl]
  apply vector_eq
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]

Conclusion "The rotational field has right-handed curl (0,0,1)."
