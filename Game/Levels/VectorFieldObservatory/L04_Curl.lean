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

/-- A constant scalar field has zero partial derivatives.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (a : ℝ) (p : Vec) (i : Fin 3), (2 : ℝ) * coordPartial (fun x => a) p i = (2 : ℝ) * 0 := by
  intro a p i
  have established := partial_constant a p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_constant as "partial_constant" in "Calculus"
/-- Division by a fixed scalar commutes with a partial derivative.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (f : ScalarField) (a : ℝ) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => f q / a) p i = (2 : ℝ) * (coordPartial f p i / a) := by
  intro f a p i
  have established := partial_div_const f a p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_div_const as "partial_div_const" in "Calculus"
/-- Negating a field negates its partial derivatives.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (f : ScalarField) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => -f q) p i = (2 : ℝ) * -coordPartial f p i := by
  intro f p i
  have established := partial_neg f p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_neg as "partial_neg" in "Calculus"
NewTheorem VectorCalculus.partial_constant VectorCalculus.partial_div_const VectorCalculus.partial_neg
/-- Right-handed curl: the three differences of cross-coordinate partial derivatives in cyclic coordinate order. -/
DefinitionDoc VectorCalculus.curl as "curl" in "Calculus notation"
NewDefinition VectorCalculus.curl

/-- Compute an oriented curl from coordinate partial derivatives.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) • curl rotation p = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  intro p
  have established := exercise_VectorFieldObservatory_4 p
  rw [established]
``` -/
TheoremDoc exercise_VectorFieldObservatory_4 as "exercise_VectorFieldObservatory_4" in "[anonymous]"

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
