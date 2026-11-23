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

/-- The product xy has coordinate partials y, x, and zero. -/
TheoremDoc VectorCalculus.partial_xy as "partial_xy" in "Calculus"
NewTheorem VectorCalculus.partial_xy

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
