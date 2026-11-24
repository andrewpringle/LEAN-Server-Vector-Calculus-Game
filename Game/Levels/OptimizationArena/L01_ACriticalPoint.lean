import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 1
Title "A critical point"

Introduction "Objective: Find all critical points of a quadratic function.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities.\n\nFind every critical point of x²+y² by setting both first partials equal to zero. The notation `h.1` and `h.2` retrieves the first and second facts of a conjunction h, just as reading components retrieves coordinates of a vector. Solve both directions: stationarity forces the origin, and the origin satisfies stationarity.\n\nWorked example: For f=(x-1)²+y², setting the two first partials to zero locates (1,0). Locating a critical point does not yet classify it.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Find all critical points of a quadratic function.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Reverse an equivalence with `.symm`. This is a lemma applied to an existing proof, rather than an additional tactic.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y : ℝ),
  x = 0 ∧ y = 0 ↔
    partialX (fun a b => a ^ 2 + b ^ 2) x y = 0 ∧ partialY (fun a b => a ^ 2 + b ^ 2) x y = 0 := by
  intro x y
  have established := exercise_OptimizationArena_1 x y
  exact established.symm
``` -/
TheoremDoc exercise_OptimizationArena_1 as "exercise_OptimizationArena_1" in "[anonymous]"

/-- Find all critical points of a quadratic function. -/
Statement exercise_OptimizationArena_1 (x y : ℝ) : (partialX (fun a b => a^2+b^2) x y = 0 ∧ partialY (fun a b => a^2+b^2) x y = 0) ↔ (x=0 ∧ y=0) := by
  Hint "1. Compute both first partials before solving any equations."
  Hint (hidden := true) "2. Use `constructor` to prove both directions of the equivalence."
  Hint (hidden := true) "3. Read the two conditions as `h.1` and `h.2`; normalize each computed equation, then assemble the origin conditions."
  constructor
  · intro h
    constructor
    · have first := h.1
      norm_num [partialX, deriv_add_const, deriv_pow_field] at first
      exact first
    · have second := h.2
      norm_num [partialY, deriv_const_add, deriv_pow_field] at second
      exact second
  · intro h
    constructor
    · norm_num [partialX, deriv_add_const, deriv_pow_field, h.1]
    · norm_num [partialY, deriv_const_add, deriv_pow_field, h.2]

Conclusion "The origin is the unique critical point of the quadratic."
