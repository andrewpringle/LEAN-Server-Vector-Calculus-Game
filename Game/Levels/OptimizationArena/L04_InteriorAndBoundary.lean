import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 4
Title "Interior and boundary"

Introduction "Objective: Compare global values over a closed disk, including its boundary.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Earlier levels of Optimization Arena.\n\nOn the closed disk x²+y²≤1, compare values at every feasible point. The lower bound follows from the nonnegativity of the two squares; the upper bound is the region constraint. The origin attains 0, and every point of the unit-circle boundary attains 1. Bounds for arbitrary feasible points provide the global justification.\n\nExercise: prove the statement below."

/-- A sum of two nonnegative real numbers is nonnegative.

### Worked usage example

Supply the sign of each summand explicitly.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  exact add_nonneg hx hy
``` -/
TheoremDoc add_nonneg as "add_nonneg" in "Calculus"
NewTheorem add_nonneg

/-- Compare global values over a closed disk, including its boundary.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Double an established bound. The positive multiplier preserves the inequality; `linarith` combines the supplied linear facts.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y : ℝ), x ^ 2 + y ^ 2 ≤ 1 → (2 : ℝ) * 0 ≤ (2 : ℝ) * (x ^ 2 + y ^ 2) := by
  intro x y h
  have established := (exercise_OptimizationArena_4 x y h).left
  linarith [established]
``` -/
TheoremDoc exercise_OptimizationArena_4 as "exercise_OptimizationArena_4" in "[anonymous]"

/-- Compare global values over a closed disk, including its boundary. -/
Statement exercise_OptimizationArena_4 (x y : ℝ) (h : x^2+y^2 ≤ 1) : 0 ≤ x^2+y^2 ∧ x^2+y^2 ≤ 1 := by
  Hint "1. Separate the lower and upper bounds."
  Hint (hidden := true) "2. Prove the lower bound by adding two nonnegative squares."
  Hint (hidden := true) "3. Use the given feasibility inequality for the upper bound."
  constructor
  · apply add_nonneg
    · exact sq_nonneg x
    · exact sq_nonneg y
  · exact h

Conclusion "Every feasible disk point has objective value between 0 and 1."
