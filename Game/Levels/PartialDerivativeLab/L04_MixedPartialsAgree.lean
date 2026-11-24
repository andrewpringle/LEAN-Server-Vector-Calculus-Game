import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 4
Title "Mixed partials agree"

Introduction "Objective: Verify mixed partial equality for an explicitly smooth polynomial.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals. Earlier levels of Partial Derivative Lab.\n\nFor the smooth polynomial xy, the first partials are y and x. Differentiating in the other variable gives 1 in both orders. This calculation proves equality for this smooth example, without assuming a general interchange theorem. Identify the fixed factor before choosing the multiplication rule.\n\nExercise: prove the statement below."

/-- A fixed left scalar factor pulls outside the scalar derivative.

### Worked usage example

Specialize the scalar derivative rule to a real-valued function and a fixed numerical constant.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => 7 * f s) t = 7 * deriv f t := by
  rw [deriv_const_mul_field]
``` -/
TheoremDoc deriv_const_mul_field as "deriv_const_mul_field" in "Calculus"
/-- A fixed right scalar factor pulls outside the scalar derivative.

### Worked usage example

Specialize the scalar derivative rule to a real-valued function and a fixed numerical constant.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => f s * 5) t = deriv f t * 5 := by
  rw [deriv_mul_const_field]
``` -/
TheoremDoc deriv_mul_const_field as "deriv_mul_const_field" in "Calculus"
NewTheorem deriv_const_mul_field deriv_mul_const_field

/-- Verify mixed partial equality for an explicitly smooth polynomial.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y : ℝ),
  (2 : ℝ) * partialY (fun s t => partialX (fun a b => a * b) s t) x y =
    (2 : ℝ) * partialX (fun s t => partialY (fun a b => a * b) s t) x y := by
  intro x y
  have established := exercise_PartialDerivativeLab_4 x y
  rw [established]
``` -/
TheoremDoc exercise_PartialDerivativeLab_4 as "exercise_PartialDerivativeLab_4" in "[anonymous]"

/-- Verify mixed partial equality for an explicitly smooth polynomial. -/
Statement exercise_PartialDerivativeLab_4 (x y : ℝ) : partialY (fun s t => partialX (fun a b => a*b) s t) x y = partialX (fun s t => partialY (fun a b => a*b) s t) x y := by
  Hint "1. Write down the first partial in each variable."
  Hint (hidden := true) "2. Use `deriv_mul_const_field` and `deriv_const_mul_field` for fixed factors."
  Hint (hidden := true) "3. Both remaining derivatives are derivatives of the identity function."
  simp only [partialX, partialY, deriv_mul_const_field, deriv_const_mul_field]
  norm_num

Conclusion "The two mixed partials of the smooth product xy are equal."
