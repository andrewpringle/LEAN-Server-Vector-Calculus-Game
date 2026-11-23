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

/-- Differentiating a coordinate gives one in its own direction and zero otherwise. -/
TheoremDoc VectorCalculus.partial_coordinate as "partial_coordinate" in "Calculus"
NewTheorem VectorCalculus.partial_coordinate

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
