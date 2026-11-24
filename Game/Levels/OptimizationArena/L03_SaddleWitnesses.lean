import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "OptimizationArena"
Level 3
Title "Saddle witnesses"

Introduction "Objective: Exhibit both upward and downward directions arbitrarily near a saddle.\n\nMathematical prerequisites: First and second partial derivatives; compact regions; elementary inequalities. Earlier levels of Optimization Arena.\n\nFor x²-y², the displacements (t,0) and (0,t) give t² and -t². For every nonzero t they lie on opposite sides of the critical value. Since t may be arbitrarily small, these witnesses explain the saddle behaviour. Begin by establishing the sign of t² once and reusing it.\n\nExercise: prove the statement below."


/-- Exhibit both upward and downward directions arbitrarily near a saddle.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Double an established bound. The positive multiplier preserves the inequality; `linarith` combines the supplied linear facts.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (t : ℝ), t ≠ 0 → (2 : ℝ) * 0 < (2 : ℝ) * (t ^ 2 - 0 ^ 2) := by
  intro t ht
  have established := (exercise_OptimizationArena_3 t ht).left
  linarith [established]
``` -/
TheoremDoc exercise_OptimizationArena_3 as "exercise_OptimizationArena_3" in "[anonymous]"

/-- Exhibit both upward and downward directions arbitrarily near a saddle. -/
Statement exercise_OptimizationArena_3 (t : ℝ) (ht : t ≠ 0) : 0 < t^2-(0:ℝ)^2 ∧ (0:ℝ)^2-t^2 < 0 := by
  Hint "1. Name the fact that a nonzero real has positive square."
  Hint (hidden := true) "2. Substitute the first displacement and use that positivity."
  Hint (hidden := true) "3. Substitute the second displacement and negate the positive value."
  have positive : 0 < t^2 := sq_pos_of_ne_zero ht
  constructor
  · norm_num
    exact positive
  · norm_num
    linarith

Conclusion "Nonzero displacements on the two coordinate paths give opposite signs, witnessing a saddle."
