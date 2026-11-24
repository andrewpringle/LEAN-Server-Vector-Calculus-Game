import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "DoubleIntegralValley"
Level 2
Title "A triangular region"

Introduction "Objective: Translate a triangular region into equivalent bounds.\n\nMathematical prerequisites: Single-variable integration; planar regions; mass and moments. Earlier levels of Double Integral Valley.\n\nFor the triangle 0≤y≤x≤1, the lower bound x≥0 follows from the other inequalities. Prove the two descriptions equivalent. For nested conjunctions, `.1` reads the first condition and `.2` reads the remaining conditions; repeat these selectors to reach later bounds. No new calculus tactic is involved.\n\nWorked example: For 0≤x≤y≤2, one may omit the separate y≥0 bound because 0≤x and x≤y imply it by transitivity.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Combine a≤b and b≤c to obtain a≤c.

### Worked usage example

Use an intermediate upper bound, then compare two numerical bounds.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) (h : x ≤ 3) : x ≤ 8 := by
  apply le_trans h
  norm_num
``` -/
TheoremDoc le_trans as "le_trans" in "Calculus"
NewTheorem le_trans

/-- Translate a triangular region into equivalent bounds.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Reverse an equivalence with `.symm`. This is a lemma applied to an existing proof, rather than an additional tactic.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y : ℝ), 0 ≤ y ∧ y ≤ x ∧ x ≤ 1 ↔ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ x := by
  intro x y
  have established := exercise_DoubleIntegralValley_2 x y
  exact established.symm
``` -/
TheoremDoc exercise_DoubleIntegralValley_2 as "exercise_DoubleIntegralValley_2" in "[anonymous]"

/-- Translate a triangular region into equivalent bounds. -/
Statement exercise_DoubleIntegralValley_2 (x y : ℝ) : (0≤x ∧ x≤1 ∧ 0≤y ∧ y≤x) ↔ (0≤y ∧ y≤x ∧ x≤1) := by
  Hint "1. Use `constructor` to prove both implications."
  Hint (hidden := true) "2. Read the required bounds from the hypothesis using `.1` and `.2`."
  Hint (hidden := true) "3. In the reverse direction, use transitivity on 0≤y and y≤x to recover 0≤x."
  constructor
  · intro bounds
    constructor
    · exact bounds.2.2.1
    · constructor
      · exact bounds.2.2.2
      · exact bounds.2.1
  · intro bounds
    constructor
    · exact le_trans bounds.1 bounds.2.1
    · constructor
      · exact bounds.2.2
      · constructor
        · exact bounds.1
        · exact bounds.2.1

Conclusion "The two sets of inequalities describe the same triangular region."
