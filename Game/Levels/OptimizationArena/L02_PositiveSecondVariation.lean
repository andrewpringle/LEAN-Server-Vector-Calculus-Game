import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 2
Title "Positive second variation"

Introduction "Objective: Classify the quadratic minimum using its positive second variation.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Earlier levels of Optimization Arena.\n\nThe two diagonal second partials of x²+y² are 2. To justify strict positivity of its second variation, a nonzero displacement has at least one nonzero coordinate. `apply Or.elim nonzero` gives the two alternatives; introduce the nonzero coordinate in each branch. Combine a strictly positive square with the other nonnegative square. A Hessian calculation is accompanied by the needed sign justification.\n\nWorked example: For f=3x²+y² the Hessian is diag(6,2). On a nonzero x-axis displacement (h,0), its quadratic form 6h² is strictly positive.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- To use a hypothesis P or Q, prove the goal assuming P and prove it again assuming Q. apply Or.elim h produces these two branches. -/
TheoremDoc Or.elim as "elim" in "Calculus"
/-- A nonnegative first summand plus a positive second summand is positive. -/
TheoremDoc add_pos_of_nonneg_of_pos as "add_pos_of_nonneg_of_pos" in "Calculus"
/-- A positive first summand plus a nonnegative second summand is positive. -/
TheoremDoc add_pos_of_pos_of_nonneg as "add_pos_of_pos_of_nonneg" in "Calculus"
/-- A nonzero real number has a strictly positive square. Supply the proof that the number is nonzero. -/
TheoremDoc sq_pos_of_ne_zero as "sq_pos_of_ne_zero" in "Calculus"
NewTheorem Or.elim add_pos_of_nonneg_of_pos add_pos_of_pos_of_nonneg sq_pos_of_ne_zero

/-- Classify the quadratic minimum using its positive second variation. -/
Statement exercise_OptimizationArena_2 : (partialX (fun x y => partialX (fun a b => a^2+b^2) x y) 0 0 = 2 ∧ partialY (fun x y => partialY (fun a b => a^2+b^2) x y) 0 0 = 2) ∧ ∀ h k : ℝ, (h≠0 ∨ k≠0) → 0 < h^2+k^2 := by
  Hint "1. Calculate the two diagonal second partials."
  Hint (hidden := true) "2. For positivity, use `Or.elim` on the nonzero-coordinate alternative."
  Hint (hidden := true) "3. Apply the appropriate positive-plus-nonnegative addition rule and the square sign lemmas."
  constructor
  · constructor
    · norm_num [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
    · norm_num [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
  · intro h k nonzero
    apply Or.elim nonzero
    · intro hh
      apply add_pos_of_pos_of_nonneg
      · exact sq_pos_of_ne_zero hh
      · exact sq_nonneg k
    · intro hk
      apply add_pos_of_nonneg_of_pos
      · exact sq_nonneg h
      · exact sq_pos_of_ne_zero hk

Conclusion "Positive second derivatives and a positive second variation justify the minimum classification."
