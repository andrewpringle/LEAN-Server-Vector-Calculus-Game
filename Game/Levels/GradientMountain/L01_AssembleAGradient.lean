import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 1
Title "Assemble a gradient"

Introduction "Objective: Compute a gradient from coordinate partial derivatives.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices.\n\nThe gradient collects the scalar partial derivatives in coordinate order. Open it using `gradient_components`. The rule `partial_coordinate` says that differentiating a coordinate with respect to itself gives 1, while the other coordinate derivatives are zero.\n\nWorked example: For f(x,y,z)=3x, the three partials are 3, 0, and 0, assembled in that order into the gradient.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Differentiating a coordinate gives one in its own direction and zero otherwise.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (j : Fin 3) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => q j) p i = (2 : ℝ) * if i = j then 1 else 0 := by
  intro j p i
  have established := partial_coordinate j p i
  rw [established]
``` -/
TheoremDoc VectorCalculus.partial_coordinate as "partial_coordinate" in "Calculus"
NewTheorem VectorCalculus.partial_coordinate

/-- Compute a gradient from coordinate partial derivatives.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) • gradient (fun q => q 0) p = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  intro p
  have established := exercise_GradientMountain_1 p
  rw [established]
``` -/
TheoremDoc exercise_GradientMountain_1 as "exercise_GradientMountain_1" in "[anonymous]"

/-- Compute a gradient from coordinate partial derivatives. -/
Statement exercise_GradientMountain_1 (p : Vec) : gradient (fun q => q 0) p = (![1,0,0] : Vec) := by
  Hint "1. Display the gradient components."
  Hint (hidden := true) "2. Compare vectors with `vector_eq`."
  Hint (hidden := true) "3. Apply `partial_coordinate` in each component."
  rw [gradient_components]
  apply vector_eq
  · norm_num [partial_coordinate]
  · norm_num [partial_coordinate]
  · norm_num [partial_coordinate]

Conclusion "The first coordinate has gradient (1,0,0)."
