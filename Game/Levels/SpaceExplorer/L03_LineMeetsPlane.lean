import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 3
Title "Line meets plane"

Introduction "Objective: Find a point satisfying both geometric constraints.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Earlier levels of Space Explorer.\n\nA line-plane intersection must satisfy two geometric conditions. The vertical line reaches height 3 at parameter 3. Supply that witness for line membership, then independently check the plane equation. This is an application of existence, vector comparison, and dot products.\n\nExercise: prove the statement below."


/-- Find a point satisfying both geometric constraints. -/
Statement exercise_SpaceExplorer_3 : onLine ![0, 0, 0] ![0, 0, 1] ![0, 0, 3] ∧ onPlane ![0, 0, 1] ![0, 0, 3] ![0, 0, 3] := by
  Hint "1. Separate line membership and plane membership."
  Hint (hidden := true) "2. For the line, supply parameter 3 and compare components."
  Hint (hidden := true) "3. For the plane, open `onPlane` and `dot`; the displacement is zero."
  constructor
  · use 3
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · rw [onPlane, dot]
    norm_num

Conclusion "The chosen point belongs to both the line and the plane."
