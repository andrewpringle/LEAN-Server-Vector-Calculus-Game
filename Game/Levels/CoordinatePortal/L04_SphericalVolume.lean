import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 4
Title "Spherical volume"

Introduction "Objective: Evaluate the spherical volume density on its standard domain.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities. Earlier levels of Coordinate Portal.\n\nOn 0≤r≤1, 0≤φ≤π, 0≤θ≤2π, the spherical factor is r² sin φ. First justify the absolute-value sign using nonnegativity of a square and of sine on [0,π]. Then perform the radial, polar-angle, and azimuth integrations in that order. This is a proved coordinate-integral calculation; identification with a Cartesian ball by a general substitution theorem remains deferred.\n\nExercise: prove the statement below."

/-- Sine is nonnegative on the closed interval from 0 to π. Supply both interval bounds. -/
TheoremDoc Real.sin_nonneg_of_mem_Icc as "sin_nonneg_of_mem_Icc" in "Calculus"
/-- The integral of sine on a..b is cos a minus cos b. -/
TheoremDoc integral_sin as "integral_sin" in "Calculus"
/-- A fixed right-hand real factor may be pulled outside an interval integral. -/
TheoremDoc intervalIntegral.integral_mul_const as "integral_mul_const" in "Calculus"
/-- A product of two nonnegative real numbers is nonnegative. Prove the sign of each factor. -/
TheoremDoc mul_nonneg as "mul_nonneg" in "Calculus"
NewTheorem Real.sin_nonneg_of_mem_Icc integral_sin intervalIntegral.integral_mul_const mul_nonneg

/-- Evaluate the spherical volume density on its standard domain. -/
Statement exercise_CoordinatePortal_4 : (∀ r p : ℝ, 0≤p → p≤Real.pi → |r^2*Real.sin p| = r^2*Real.sin p) ∧ (∫ t : ℝ in 0..(2*Real.pi), ∫ p : ℝ in 0..Real.pi, ∫ r : ℝ in 0..1, r^2*Real.sin p) = 4*Real.pi/3 := by
  Hint "1. Prove the sign of the spherical factor from the stated polar-angle bounds."
  Hint (hidden := true) "2. Name the radial integral, treating sin φ as a constant."
  Hint (hidden := true) "3. Integrate sine on [0,π], then the constant on [0,2π]."
  constructor
  · intro r p lower upper
    apply abs_of_nonneg
    apply mul_nonneg
    · exact sq_nonneg r
    · apply Real.sin_nonneg_of_mem_Icc
      constructor
      · exact lower
      · exact upper
  · have radial (p : ℝ) : (∫ r : ℝ in 0..1, r^2*Real.sin p) = (1/3)*Real.sin p := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      norm_num
    have polar : (∫ p : ℝ in 0..Real.pi, ∫ r : ℝ in 0..1, r^2*Real.sin p) = 2/3 := by
      rw [integral_values radial, intervalIntegral.integral_const_mul, integral_sin]
      norm_num
    rw [polar, constant_integral]
    ring

Conclusion "The spherical factor has the required sign, and its coordinate-side volume integral is 4π/3."
