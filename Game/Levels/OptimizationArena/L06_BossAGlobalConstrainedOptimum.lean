import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 6
Title "Boss: a global constrained optimum"

Introduction "Objective: Prove a feasible point attains a global optimum.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Earlier levels of Optimization Arena.\n\nVerify the proposed optimizer (1,1) lies on the constraint and has value 2. For an arbitrary feasible point, the identity (x+y)²+(x-y)²=2(x²+y²) and a nonnegative square bound the objective by 2. This proves a global maximum, not merely a stationary candidate. Use the square-bound method from Gradient Mountain.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Prove a feasible point attains a global optimum.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ((1 : ℝ)^2 + 1^2) = 4 := by
  rw [exercise_OptimizationArena_6.1.1]
  norm_num
``` -/
TheoremDoc exercise_OptimizationArena_6 as "exercise_OptimizationArena_6" in "[anonymous]"

/-- Prove a feasible point attains a global optimum. -/
Statement exercise_OptimizationArena_6 : ((1:ℝ)^2+1^2=2 ∧ (1:ℝ)+1=2) ∧ ∀ x y : ℝ, x^2+y^2=2 → x+y≤2 := by
  Hint "1. Check feasibility and the attained objective value."
  Hint (hidden := true) "2. For arbitrary feasible x and y, use the sum-and-difference square identity."
  Hint (hidden := true) "3. Discard the nonnegative square and apply `le_of_sq_le_sq` with upper bound 2."
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro x y feasible
    have identity : (x+y)^2+(x-y)^2 = 2*(x^2+y^2) := by ring
    rw [feasible] at identity
    have nonnegative : 0 ≤ (x-y)^2 := sq_nonneg _
    have squared : (x+y)^2 ≤ (2:ℝ)^2 := by linarith
    apply le_of_sq_le_sq squared
    norm_num

Conclusion "The feasible point (1,1) attains 2, and no feasible point has a larger value."
