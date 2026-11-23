import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 6
Title "Boss: three points"

Introduction "Objective: Build a nondegenerate plane through three points.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Earlier levels of Space Explorer.\n\nUse the edges AB and AC to compute a normal to the plane through the three specified points. Show the cross product is nonzero by its z component, using `vector_ne_zero`. Then verify the point-normal equation for B and C; A is already the base point. A nonzero cross product also establishes that the three points are not collinear.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- A vector with a nonzero component is nonzero. -/
TheoremDoc VectorCalculus.vector_ne_zero as "vector_ne_zero" in "Calculus"
NewTheorem VectorCalculus.vector_ne_zero

/-- Build a nondegenerate plane through three points. -/
Statement exercise_SpaceExplorer_6 : cross (![1,0,0] - ![0,0,0]) (![0,1,0] - ![0,0,0]) = (![0,0,1] : Vec) ∧ (![0,0,1] : Vec) ≠ 0 ∧ onPlane ![0,0,1] ![0,0,0] ![1,0,0] ∧ onPlane ![0,0,1] ![0,0,0] ![0,1,0] := by
  Hint "1. Separate the four claims with repeated `constructor`."
  Hint (hidden := true) "2. Compute the cross product, and use `vector_ne_zero 2` for its nonzero component."
  Hint (hidden := true) "3. Check B and C in `onPlane` using the normal you found."
  constructor
  · apply vector_eq
    · norm_num [cross]
    · norm_num [cross]
    · norm_num [cross]
  · constructor
    · apply vector_ne_zero 2
      norm_num
    · constructor
      · rw [onPlane, dot]
        norm_num
      · rw [onPlane, dot]
        norm_num

Conclusion "A nonzero cross product supplies a plane normal for the three noncollinear points."
