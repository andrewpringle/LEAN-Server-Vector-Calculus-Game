import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 4
Title "Distance to a plane"

Introduction "Objective: Evaluate the normal-distance formula with a nonzero normal.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Earlier levels of Space Explorer.\n\nDistance from q to a plane is |n·(q-p)| divided by the Euclidean length of its nonzero normal. For the plane z=1, choose n=(0,0,1), whose length is 1. Absolute value makes this a nonnegative distance, independent of the side of the plane.\n\nExercise: prove the statement below."

/-- Euclidean length, the nonnegative square root of lengthSq. This differs from the default Pi-type norm. -/
DefinitionDoc VectorCalculus.length as "length" in "Calculus notation"
/-- Absolute normal displacement divided by the Euclidean normal length. The plane normal must be nonzero. -/
DefinitionDoc VectorCalculus.planeDistance as "planeDistance" in "Calculus notation"
NewDefinition VectorCalculus.length VectorCalculus.planeDistance

/-- Evaluate the normal-distance formula with a nonzero normal.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * planeDistance (![0, 0, 1] : Vec) (![0, 0, 1] : Vec) (![2, -3, 4] : Vec) = (2 : ℝ) * 3 := by
  have established := exercise_SpaceExplorer_4
  rw [established]
``` -/
TheoremDoc exercise_SpaceExplorer_4 as "exercise_SpaceExplorer_4" in "[anonymous]"

/-- Evaluate the normal-distance formula with a nonzero normal. -/
Statement exercise_SpaceExplorer_4 : planeDistance ![0, 0, 1] ![0, 0, 1] ![2, -3, 4] = 3 := by
  Hint "1. Rewrite `planeDistance` and the length definitions."
  Hint (hidden := true) "2. The displacement has normal component 4-1."
  Hint (hidden := true) "3. Evaluate the absolute value and the unit-normal denominator."
  rw [planeDistance, length, lengthSq, dot]
  norm_num [dot]

Conclusion "The point is distance 3 from the plane z=1."
