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

/-- Cancel a common nonzero left factor in a real multiplication equality. Supply the nonzero-factor proof and the equality. -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Calculus"
NewTheorem mul_left_cancel₀

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
