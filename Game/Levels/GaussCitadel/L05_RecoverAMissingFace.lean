import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 5
Title "Recover a missing face"

Introduction "Objective: Deduce an unknown flux from the closed-boundary total.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases. Earlier levels of Gauss Citadel.\n\nThe five known outward face fluxes sum to 5. Find the missing top flux by first using the unit-cube Gauss theorem to calculate total flux. The general matching-partial rule `divergence_diagonal` gives divergence 2+3+4=9. Rewrite the balance equation and solve the remaining linear equation. The balance assumption states the geometric decomposition, not the requested missing value.\n\nExercise: prove the statement below."

/-- Matching diagonal partials give the divergence of a diagonal linear field.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (a b c : ℝ) (p : Vec), (2 : ℝ) * divergence (fun q => (![a * q 0, b * q 1, c * q 2] : Vec)) p = (2 : ℝ) * (a + b + c) := by
  intro a b c p
  have established := divergence_diagonal a b c p
  rw [established]
``` -/
TheoremDoc VectorCalculus.divergence_diagonal as "divergence_diagonal" in "Calculus"
NewTheorem VectorCalculus.divergence_diagonal

/-- Deduce an unknown flux from the closed-boundary total.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (top : ℝ), (cubeFlux fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) = 5 + top → (2 : ℝ) * top = (2 : ℝ) * 4 := by
  intro top h
  have established := exercise_GaussCitadel_5 top h
  rw [established]
``` -/
TheoremDoc exercise_GaussCitadel_5 as "exercise_GaussCitadel_5" in "[anonymous]"

/-- Deduce an unknown flux from the closed-boundary total. -/
Statement exercise_GaussCitadel_5 (top : ℝ) (h : cubeFlux (fun p => ![2*p 0,3*p 1,4*p 2]) = 5+top) : top = 4 := by
  Hint "1. Use `gauss_diagonal` to replace total flux with a volume integral."
  Hint (hidden := true) "2. Evaluate the constant divergence using `divergence_diagonal`."
  Hint (hidden := true) "3. Substitute the total in the face balance and solve with `linarith`."
  have total : cubeFlux (fun p => ![2*p 0,3*p 1,4*p 2]) = 9 := by
    rw [gauss_diagonal]
    norm_num [divergence_diagonal]
  rw [total] at h
  linarith

Conclusion "Gauss gives total flux 9; subtracting the known contribution 5 gives missing flux 4."
