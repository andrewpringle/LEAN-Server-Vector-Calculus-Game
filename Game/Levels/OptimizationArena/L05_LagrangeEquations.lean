import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 5
Title "Lagrange equations"

Introduction "Objective: Solve the Lagrange multiplier system and find both candidates.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Earlier levels of Optimization Arena.\n\nFor x+y on x²+y²=2, the stationarity equations give 1=λ(2x) and 1=λ(2y). First show λ is nonzero, then cancel it using `mul_left_cancel₀`. The constraint gives x²=1 after x=y, and factoring produces the two signs. `left` and `right` select the candidate established in each branch. These stationary candidates still require a global comparison. `mul_eq_zero.mp factor` uses the forward direction of the product-zero equivalence to obtain the two factor alternatives.\n\nExercise: prove the statement below."

/-- Cancel a common nonzero left factor in a real multiplication equality. Supply the nonzero-factor proof and the equality.

### Worked usage example

The common factor must be nonzero before it can be cancelled.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x y : ℝ) (h : 3*x = 3*y) : x = y := by
  apply mul_left_cancel₀ (by norm_num : (3 : ℝ) ≠ 0)
  exact h
``` -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Calculus"
NewTheorem mul_left_cancel₀

/-- Solve the Lagrange multiplier system and find both candidates.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Both multiplier-system candidates have equal coordinates. The .1 and .2.1 projections extract the coordinate equalities from each conjunction.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x y l : ℝ) (hx : 1=l*(2*x)) (hy : 1=l*(2*y)) (hc : x^2+y^2=2) : x = y := by
  apply Or.elim (exercise_OptimizationArena_5 x y l hx hy hc)
  · intro h
    rw [h.1, h.2.1]
  · intro h
    rw [h.1, h.2.1]
``` -/
TheoremDoc exercise_OptimizationArena_5 as "exercise_OptimizationArena_5" in "[anonymous]"

/-- Solve the Lagrange multiplier system and find both candidates. -/
Statement exercise_OptimizationArena_5 (x y l : ℝ) (hx : 1=l*(2*x)) (hy : 1=l*(2*y)) (hc : x^2+y^2=2) : (x=1 ∧ y=1 ∧ l=1/2) ∨ (x = -1 ∧ y = -1 ∧ l = -1/2) := by
  Hint "1. Show the multiplier is nonzero and cancel it to obtain x=y."
  Hint (hidden := true) "2. Use the constraint to prove x²=1, then factor (x-1)(x+1)."
  Hint (hidden := true) "3. Handle the two factors with `Or.elim`; recover y and λ for each sign."
  have multiplier : l ≠ 0 := by
    intro zero
    rw [zero] at hx
    norm_num at hx
  have same : l*(2*x) = l*(2*y) := by
    rw [← hx, ← hy]
  have twice : 2*x = 2*y := mul_left_cancel₀ multiplier same
  have equal : x = y := by linarith
  have square : x^2 = 1 := by
    rw [← equal] at hc
    linarith
  have factor : (x-1)*(x+1) = 0 := by
    have expansion : (x-1)*(x+1) = x^2-1 := by ring
    rw [expansion, square]
    norm_num
  apply Or.elim (mul_eq_zero.mp factor)
  · intro plus
    left
    have xvalue : x = 1 := by linarith
    constructor
    · exact xvalue
    · constructor
      · rw [← equal]
        exact xvalue
      · rw [xvalue] at hx
        linarith
  · intro minus
    right
    have xvalue : x = -1 := by linarith
    constructor
    · exact xvalue
    · constructor
      · rw [← equal]
        exact xvalue
      · rw [xvalue] at hx
        linarith

Conclusion "The stationarity system and constraint yield exactly the two listed candidates."
