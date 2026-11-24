import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 2
Title "Recognize a gradient"

Introduction "Objective: Verify that a field has a specified potential.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Earlier levels of Vector Field Observatory.\n\nFor the globally defined scalar potential φ=xy, calculate its gradient as (y,x,0). Use the product partial rule `partial_xy` with the component gradient formula. Producing an actual potential proves this field is conservative on all of space; no curl-free domain shortcut is needed.\n\nWorked example: For φ=xz, holding the other coordinates fixed gives gradient (z,0,x). A proposed potential is verified by all three partial derivatives.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- The product xy has coordinate partials y, x, and zero.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => q 0 * q 1) p i = (2 : ℝ) * if i = 0 then p 1 else if i = 1 then p 0 else 0 := by
  intro p i
  have established := partial_xy p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_xy as "partial_xy" in "Calculus"
NewTheorem VectorCalculus.partial_xy

/-- Verify that a field has a specified potential.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) • gradient (fun q => q 0 * q 1) p = (2 : ℝ) • (![p 1, p 0, 0] : Vec) := by
  intro p
  have established := exercise_VectorFieldObservatory_2 p
  rw [established]
``` -/
TheoremDoc exercise_VectorFieldObservatory_2 as "exercise_VectorFieldObservatory_2" in "[anonymous]"

/-- Verify that a field has a specified potential. -/
Statement exercise_VectorFieldObservatory_2 (p : Vec) : gradient (fun q => q 0*q 1) p = (![p 1,p 0,0] : Vec) := by
  Hint "1. Display the gradient as three partial derivatives."
  Hint (hidden := true) "2. Use `vector_eq`."
  Hint (hidden := true) "3. Evaluate the three entries with `partial_xy`."
  rw [gradient_components]
  apply vector_eq
  · norm_num [partial_xy]
  · norm_num [partial_xy]
  · norm_num [partial_xy]

Conclusion "The globally defined potential xy has gradient (y,x,0)."
