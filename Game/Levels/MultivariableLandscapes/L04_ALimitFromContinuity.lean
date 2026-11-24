import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 4
Title "A limit from continuity"

Introduction "Objective: Evaluate a multivariable limit using continuity.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity. Earlier levels of Multivariable Landscapes.\n\n`LimitAtOrigin f L` is a readable name for the actual full neighborhood limit of f at the origin. The proved theorem `limit_of_continuous` asks for continuity and the value f(0)=L. Reuse the continuity method and calculate the value separately. This is the standard continuity method for evaluating a multivariable limit.\n\nExercise: prove the statement below."

/-- Continuity and the value at zero give the full limit.

### Worked usage example

A full multivariable limit follows from continuity and the actual value at the origin.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f : ScalarField) (hc : Continuous f) (hv : f 0 = 4) : LimitAtOrigin f 4 := by
  exact limit_of_continuous hc hv
``` -/
TheoremDoc VectorCalculus.limit_of_continuous as "limit_of_continuous" in "Calculus"
NewTheorem VectorCalculus.limit_of_continuous
/-- A readable name for the full multivariable limit at the origin. -/
DefinitionDoc VectorCalculus.LimitAtOrigin as "LimitAtOrigin" in "Calculus notation"
NewDefinition VectorCalculus.LimitAtOrigin

/-- Evaluate a multivariable limit using continuity.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use uniqueness of limits to rule out any different proposed value. tendsto_nhds_unique compares two limits of the same function along the same nontrivial filter.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (L : ℝ) (h : LimitAtOrigin squarePotential L) : L = 0 := by
  exact tendsto_nhds_unique h exercise_MultivariableLandscapes_4
``` -/
TheoremDoc exercise_MultivariableLandscapes_4 as "exercise_MultivariableLandscapes_4" in "[anonymous]"

/-- Evaluate a multivariable limit using continuity. -/
Statement exercise_MultivariableLandscapes_4 : LimitAtOrigin squarePotential 0 := by
  Hint "1. Apply `limit_of_continuous`."
  Hint (hidden := true) "2. Prove continuity using the sum-of-squares rule."
  Hint (hidden := true) "3. Evaluate the function at the origin."
  apply limit_of_continuous
  · apply continuous_sum_squares
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_apply 2
  · norm_num [squarePotential]

Conclusion "Continuity and the origin value establish the actual multivariable limit."
