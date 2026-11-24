import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 3
Title "Reverse the order"

Introduction "Objective: Verify reversed bounds by evaluating both integrals.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments. Earlier levels of Double Integral Valley.\n\nThe same triangle has bounds 0≤y≤x≤1 or 0≤y≤1 with y≤x≤1. For density 1, compute the inner integrals as x and 1-y. `integral_values` substitutes these pointwise formulas under the outer integrals. Splitting an integral of a difference requires integrability; continuity of 1 and y on this bounded interval supplies it. This is a directly verified order-reversal special case.\n\nExercise: prove the statement below."

/-- Integrate the identity function using (b²-a²)/2.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {a b : ℝ}, (2 : ℝ) * ∫ (x : ℝ) in a..b, x = (2 : ℝ) * ((b ^ 2 - a ^ 2) / 2) := by
  intro a b
  have established := integral_id (a := a) (b := b)
  rw [established]
``` -/
TheoremDoc integral_id as "integral_id" in "Calculus"
/-- Split an integral of f-g into the difference of integrals. Both functions must be interval integrable.

### Worked usage example

Both integrability assumptions are needed to split a difference.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 4) (hg : IntervalIntegrable g volume 0 4) :
    (∫ t : ℝ in 0..4, f t-g t) = (∫ t : ℝ in 0..4, f t) - (∫ t : ℝ in 0..4, g t) := by
  rw [intervalIntegral.integral_sub hf hg]
``` -/
TheoremDoc intervalIntegral.integral_sub as "integral_sub" in "Calculus"
NewTheorem integral_id intervalIntegral.integral_sub

/-- Verify reversed bounds by evaluating both integrals.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) in 0..1, ∫ (y : ℝ) in 0..x, (1 : ℝ) = (2 : ℝ) * ∫ (y : ℝ) in 0..1, ∫ (x : ℝ) in y..1, (1 : ℝ) := by
  have established := exercise_DoubleIntegralValley_3
  rw [established]
``` -/
TheoremDoc exercise_DoubleIntegralValley_3 as "exercise_DoubleIntegralValley_3" in "[anonymous]"

/-- Verify reversed bounds by evaluating both integrals. -/
Statement exercise_DoubleIntegralValley_3 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..x, (1:ℝ)) = ∫ y : ℝ in 0..1, ∫ x : ℝ in y..1, (1:ℝ) := by
  Hint "1. Name both inner integrals as functions of the outer variable."
  Hint (hidden := true) "2. Replace them with `integral_values`."
  Hint (hidden := true) "3. Use the difference rule with the displayed continuity-based integrability proofs, then `integral_id`."
  have forward (x : ℝ) : (∫ y : ℝ in 0..x, (1:ℝ)) = x := by
    rw [constant_integral]
    ring
  have backward (y : ℝ) : (∫ x : ℝ in y..1, (1:ℝ)) = 1-y := by
    rw [constant_integral]
    ring
  rw [integral_values forward, integral_values backward]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun y : ℝ => y) (continuous_const.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)]
  norm_num [integral_id]

Conclusion "Both integration orders give the same area for this explicitly calculated triangle."
