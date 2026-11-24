import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 3
Title "Second derivatives"

Introduction "Objective: Differentiate an already computed first partial.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals. Earlier levels of Partial Derivative Lab.\n\nA second partial differentiates an already computed first partial. For x²+y² the first x partial is 2x. Differentiating it again in x gives 2, while differentiating it in y gives 0. `simp only [rules]` applies just the displayed derivative rules, including under the inner function; this is the explicit-rule form of the simplification tool already learned.\n\nExercise: prove the statement below."

/-- A constant scalar function has derivative zero.

### Worked usage example

A different constant field has zero scalar derivative.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : deriv (fun _ : ℝ => (9 : ℝ)) t = 0 := by
  exact deriv_const t 9
``` -/
TheoremDoc deriv_const as "deriv_const" in "Calculus"
NewTheorem deriv_const

/-- Differentiate an already computed first partial.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y : ℝ), (2 : ℝ) * partialX (fun s t => partialX (fun a b => a ^ 2 + b ^ 2) s t) x y = (2 : ℝ) * 2 := by
  intro x y
  have established := (exercise_PartialDerivativeLab_3 x y).left
  rw [established]
``` -/
TheoremDoc exercise_PartialDerivativeLab_3 as "exercise_PartialDerivativeLab_3" in "[anonymous]"

/-- Differentiate an already computed first partial. -/
Statement exercise_PartialDerivativeLab_3 (x y : ℝ) : partialX (fun s t => partialX (fun a b => a^2+b^2) s t) x y = 2 ∧ partialY (fun s t => partialX (fun a b => a^2+b^2) s t) x y = 0 := by
  Hint "1. Separate the xx derivative from the yx derivative."
  Hint (hidden := true) "2. Simplify the inner partial using the rules from the preceding levels."
  Hint (hidden := true) "3. Differentiate 2x in the requested variable using `deriv_const_mul_id` or `deriv_const`."
  constructor
  · simp only [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
    norm_num
  · simp only [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id, deriv_const]

Conclusion "The xx partial is 2 and the yx partial is zero."
