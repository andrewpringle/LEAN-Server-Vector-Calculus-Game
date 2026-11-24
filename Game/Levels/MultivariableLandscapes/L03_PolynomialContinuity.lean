import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 3
Title "Polynomial continuity"

Introduction "Objective: Prove joint continuity of a polynomial in three variables.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity. Earlier levels of Multivariable Landscapes.\n\n`Continuous f` means joint continuity in all coordinates. The rule `continuous_sum_squares` says that squaring and adding three continuous scalar functions preserves continuity. Apply it and supply continuity of each coordinate projection with `continuous_apply 0`, `1`, and `2`. No filter manipulation is needed.\n\nExercise: prove the statement below."

/-- A sum of squared continuous real functions is continuous.

### Worked usage example

Joint continuity of three real fields implies continuity of their sum of squares at the displayed spatial point. The .continuousAt lemma specializes global continuity to a point.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f g h : ScalarField) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ContinuousAt (fun p => f p^2 + g p^2 + h p^2) (![2, 3, 0] : Vec) := by
  exact (continuous_sum_squares hf hg hh).continuousAt
``` -/
TheoremDoc VectorCalculus.continuous_sum_squares as "continuous_sum_squares" in "Calculus"
/-- A coordinate projection on a product space is continuous. Supply its coordinate index, for example continuous_apply 0.

### Worked usage example

A coordinate projection is continuous; the index 2 selects the third coordinate.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : Continuous (fun p : Vec => p 2) := by
  exact continuous_apply 2
``` -/
TheoremDoc continuous_apply as "continuous_apply" in "Calculus"
NewTheorem VectorCalculus.continuous_sum_squares continuous_apply
/-- Joint continuity of a function at every point of its domain. The sum, power, and coordinate continuity rules build proofs. -/
DefinitionDoc Continuous as "Continuous" in "Calculus notation"
NewDefinition Continuous

/-- Prove joint continuity of a polynomial in three variables.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the completed global-continuity result at a new point. The .continuousAt lemma passes from global continuity to continuity at one point.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ContinuousAt squarePotential (![2, 0, 1] : Vec) := by
  exact exercise_MultivariableLandscapes_3.continuousAt
``` -/
TheoremDoc exercise_MultivariableLandscapes_3 as "exercise_MultivariableLandscapes_3" in "[anonymous]"

/-- Prove joint continuity of a polynomial in three variables. -/
Statement exercise_MultivariableLandscapes_3 : Continuous squarePotential := by
  Hint "1. Apply `continuous_sum_squares` to the three coordinate functions."
  Hint (hidden := true) "2. This creates one continuity goal per coordinate."
  Hint (hidden := true) "3. Use `exact continuous_apply 0`, and similarly for coordinates 1 and 2."
  apply continuous_sum_squares
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2

Conclusion "Continuity follows from continuity of the coordinate functions and polynomial operations."
