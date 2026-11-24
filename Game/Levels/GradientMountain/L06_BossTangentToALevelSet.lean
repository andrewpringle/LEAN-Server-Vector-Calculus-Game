import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 6
Title "Boss: tangent to a level set"

Introduction "Objective: Relate a level-set equation, its gradient, and tangent directions.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices. Earlier levels of Gradient Mountain.\n\nFor f(p)=p₀, the level surface f=2 is a plane. A tangent displacement has first coordinate zero, so it preserves the level equation. Compute the gradient and verify its dot product with the tangent direction is zero. This links an equation, a derivative, and geometry without introducing new proof tools.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Relate a level-set equation, its gradient, and tangent directions.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p v : Vec), p 0 = 2 → v 0 = 0 → (2 : ℝ) * (p + v) 0 = (2 : ℝ) * 2 := by
  intro p v hp hv
  have established := (exercise_GradientMountain_6 p v hp hv).left
  rw [established]
``` -/
TheoremDoc exercise_GradientMountain_6 as "exercise_GradientMountain_6" in "[anonymous]"

/-- Relate a level-set equation, its gradient, and tangent directions. -/
Statement exercise_GradientMountain_6 (p v : Vec) (hp : p 0 = 2) (hv : v 0 = 0) : (p+v) 0 = 2 ∧ dot (gradient (fun q => q 0) p) v = 0 := by
  Hint "1. Use the level equation and the zero first component to check p+v."
  Hint (hidden := true) "2. Display the gradient of the first coordinate."
  Hint (hidden := true) "3. Calculate its dot product with v."
  constructor
  · simp [hv, hp]
  · rw [gradient_components]
    norm_num [dot, partial_coordinate, hv]

Conclusion "A tangent displacement preserves the level plane and is perpendicular to its gradient."
