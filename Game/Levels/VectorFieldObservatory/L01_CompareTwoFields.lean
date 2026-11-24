import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 1
Title "Compare two fields"

Introduction "Objective: Evaluate and distinguish vector fields at a point.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors.\n\nA vector field assigns a vector to each position. The radial field returns the position itself, while the rotational field rotates and scales its planar components. Evaluate both at the same point to compare their behaviour. Coordinate calculations now use only familiar vector methods.\n\nWorked example: For F(x,y,z)=(2x,y,0), substituting (1,3,0) gives (2,3,0). A field evaluation takes a position as input and returns a vector.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- The planar rotational field (-y/2,x/2,0), whose vertical curl is one. -/
DefinitionDoc VectorCalculus.rotation as "rotation" in "Calculus notation"
NewDefinition VectorCalculus.rotation

/-- Evaluate and distinguish vector fields at a point.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) • radial (![2, 0, 0] : Vec) = (2 : ℝ) • (![2, 0, 0] : Vec) := by
  have established := exercise_VectorFieldObservatory_1.left
  rw [established]
``` -/
TheoremDoc exercise_VectorFieldObservatory_1 as "exercise_VectorFieldObservatory_1" in "[anonymous]"

/-- Evaluate and distinguish vector fields at a point. -/
Statement exercise_VectorFieldObservatory_1 : radial ![2,0,0] = (![2,0,0] : Vec) ∧ rotation ![2,0,0] = (![0,1,0] : Vec) := by
  Hint "1. Separate the two field evaluations."
  Hint (hidden := true) "2. The radial-field identity is definitional."
  Hint (hidden := true) "3. Compare the rotational output by its three coordinates."
  constructor
  · rfl
  · apply vector_eq
    · norm_num [rotation]
    · norm_num [rotation]
    · norm_num [rotation]

Conclusion "The two vector fields give the stated different outputs at the same point."
