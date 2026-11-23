import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 5
Title "The ascent bound"

Introduction "Objective: Prove a sharp bound for a gradient dotted with a unit direction.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices. Earlier levels of Gradient Mountain.\n\nFor gradient (3,4,0), the unit-direction rate cannot exceed 5. The supplied algebraic identity `ascent_squares` decomposes 25|u|² into the squared rate and two nonnegative terms. Use the unit assumption and nonnegativity to bound the squared rate, then `le_of_sq_le_sq` with nonnegative upper bound 5. You choose and combine the estimates.\n\nExercise: prove the statement below."

/-- The identity behind the concrete (3,4,0) steepest-ascent bound. -/
TheoremDoc VectorCalculus.ascent_squares as "ascent_squares" in "Calculus"
/-- From a^2 ≤ b^2 and 0 ≤ b, conclude a ≤ b. The upper bound must be nonnegative; a may have either sign. -/
TheoremDoc le_of_sq_le_sq as "le_of_sq_le_sq" in "Calculus"
/-- Every real square is nonnegative: sq_nonneg x proves 0 ≤ x^2. -/
TheoremDoc sq_nonneg as "sq_nonneg" in "Calculus"
NewTheorem VectorCalculus.ascent_squares le_of_sq_le_sq sq_nonneg

/-- Prove a sharp bound for a gradient dotted with a unit direction. -/
Statement exercise_GradientMountain_5 (u : Vec) (hu : lengthSq u = 1) : dot ![3,4,0] u ≤ 5 := by
  Hint "1. Use `ascent_squares u` and substitute the unit-length hypothesis."
  Hint (hidden := true) "2. The two additional squares are nonnegative, so the squared rate is at most 25."
  Hint (hidden := true) "3. Apply `le_of_sq_le_sq` with upper bound 5, then identify the dot product."
  have identity := ascent_squares u
  have perpendicular : 0 ≤ (4*u 0-3*u 1)^2 := sq_nonneg _
  have vertical : 0 ≤ (u 2)^2 := sq_nonneg _
  rw [hu] at identity
  have bound : (3*u 0+4*u 1)^2 ≤ (5:ℝ)^2 := by
    linarith
  have rate : 3*u 0+4*u 1 ≤ 5 := by
    apply le_of_sq_le_sq bound
    norm_num
  norm_num [dot]
  exact rate

Conclusion "Every unit direction gives a rate at most 5 for gradient (3,4,0)."
