import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 1
Title "A positive boundary"

Introduction "Objective: Verify endpoints of counterclockwise square edges.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation.\n\nA positive planar boundary goes counterclockwise, keeping its region on the left. The square edges run right along the bottom, up the right, left along the top, and down the left. Check that the first two joins match. Their explicit parameter directions determine the orientation used by `squareCirculation`.\n\nWorked example: A circle traversed counterclockwise has its disk on the left. Positive square edges obey the same left-of-motion convention.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Verify endpoints of counterclockwise square edges.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) • (![1, 0, 0] : Vec) = (2 : ℝ) • (fun t : ℝ => (![1, t, 0] : Vec)) 0 := by
  have established := exercise_GreensGarden_1.left
  rw [established]
``` -/
TheoremDoc exercise_GreensGarden_1 as "exercise_GreensGarden_1" in "[anonymous]"

/-- Verify endpoints of counterclockwise square edges. -/
Statement exercise_GreensGarden_1 : (![1,0,0] : Vec) = (fun t : ℝ => ![1,t,0]) 0 ∧ (fun t : ℝ => (![1,t,0] : Vec)) 1 = (fun t : ℝ => ![1-t,1,0]) 0 := by
  Hint "1. Separate the two endpoint joins."
  Hint (hidden := true) "2. Substitute the appropriate parameter endpoints."
  Hint (hidden := true) "3. Use the familiar vector component comparison."
  constructor
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num

Conclusion "The specified square edges join in the positive counterclockwise traversal."
