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

/-- A sum of squared continuous real functions is continuous. -/
TheoremDoc VectorCalculus.continuous_sum_squares as "continuous_sum_squares" in "Calculus"
/-- A coordinate projection on a product space is continuous. Supply its coordinate index, for example continuous_apply 0. -/
TheoremDoc continuous_apply as "continuous_apply" in "Calculus"
NewTheorem VectorCalculus.continuous_sum_squares continuous_apply
/-- Joint continuity of a function at every point of its domain. The sum, power, and coordinate continuity rules build proofs. -/
DefinitionDoc Continuous as "Continuous" in "Calculus notation"
NewDefinition Continuous

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
