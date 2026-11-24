import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 2
Title "A unit direction"

Introduction "Objective: Compute a total directional derivative with a unit-direction assumption.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices. Earlier levels of Gradient Mountain.\n\nA directional derivative applies the total derivative to the direction u. The general coordinate-projection rule `directional_coordinate` computes it without asking you to construct a continuous linear map. The hypothesis `lengthSq u = 1` specifies a unit direction, so the answer is a rate per unit distance. The underlying derivative identity also holds for nonunit vectors.\n\nWorked example: For the scalar field f(x,y,z)=x and unit direction (0,1,0), the directional rate is zero: moving in y does not change x.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- A coordinate projection's total directional derivative is the chosen component. This rate is per unit distance when the direction has Euclidean length one.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (j : Fin 3) (p u : Vec), (2 : ℝ) * directional (fun q => q j) p u = (2 : ℝ) * u j := by
  intro j p u
  have established := directional_coordinate j p u
  rw [established]
``` -/
TheoremDoc VectorCalculus.directional_coordinate as "directional_coordinate" in "Calculus"
NewTheorem VectorCalculus.directional_coordinate
/-- Apply the total derivative to a direction vector. For a unit direction, this is rate of change per unit distance. -/
DefinitionDoc VectorCalculus.directional as "directional" in "Calculus notation"
NewDefinition VectorCalculus.directional

/-- Compute a total directional derivative with a unit-direction assumption.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p u : Vec), lengthSq u = 1 → (2 : ℝ) * directional (fun q => q 0) p u = (2 : ℝ) * u 0 := by
  intro p u hu
  have established := exercise_GradientMountain_2 p u hu
  rw [established]
``` -/
TheoremDoc exercise_GradientMountain_2 as "exercise_GradientMountain_2" in "[anonymous]"

/-- Compute a total directional derivative with a unit-direction assumption. -/
Statement exercise_GradientMountain_2 (p u : Vec) (hu : lengthSq u = 1) : directional (fun q => q 0) p u = u 0 := by
  Hint "1. Recognize the scalar function as the first coordinate projection."
  Hint (hidden := true) "2. Choose `directional_coordinate` with coordinate index 0."
  Hint (hidden := true) "3. Rewrite with that rule; the unit hypothesis provides the geometric interpretation."
  rw [directional_coordinate]

Conclusion "In a unit direction, the coordinate rate is the direction’s first component."
