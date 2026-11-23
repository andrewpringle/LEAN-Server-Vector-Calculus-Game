import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 6
Title "Boss: repair the origin"

Introduction "Objective: Prove continuity of a separately defined extension at the origin.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity. Earlier levels of Multivariable Landscapes.\n\nFilling in an exceptional point preserves continuity only when its assigned value matches the continuous extension. Apply `continuous_fill_origin`: you must prove that the polynomial is continuous and that its value at the origin is exactly the proposed replacement 0. The support rule handles the equality of the piecewise function, not these mathematical checks.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Filling in the existing value at the origin preserves continuity. -/
TheoremDoc VectorCalculus.continuous_fill_origin as "continuous_fill_origin" in "Calculus"
NewTheorem VectorCalculus.continuous_fill_origin

/-- Prove continuity of a separately defined extension at the origin. -/
Statement exercise_MultivariableLandscapes_6 : Continuous (fun p : Vec => if p = 0 then 0 else squarePotential p) := by
  Hint "1. Apply `continuous_fill_origin`."
  Hint (hidden := true) "2. Supply joint continuity of the underlying polynomial."
  Hint (hidden := true) "3. Verify that the assigned origin value matches the polynomial."
  apply continuous_fill_origin
  · apply continuous_sum_squares
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_apply 2
  · norm_num [squarePotential]

Conclusion "The assigned origin value matches the polynomial extension, making the piecewise function continuous."
