import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 6
Title "Boss: area from the boundary"

Introduction "Objective: Recover enclosed area from a boundary circulation.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation. Earlier levels of Green’s Garden.\n\nThe area formula uses the boundary field (-y/2,x/2,0), whose planar curl is 1. Compute the boundary integral directly on the four positively oriented edges, then compare with the double integral of 1. The two nonzero edge contributions are each 1/2. This proves the stated area identity for the unit square.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."


/-- Recover enclosed area from a boundary circulation. -/
Statement exercise_GreensGarden_6 : squareCirculation rotation = (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, (1:ℝ)) ∧ squareCirculation rotation = 1 := by
  Hint "1. Use the rotational field and the positive square boundary."
  Hint (hidden := true) "2. Compute and add its four work integrals."
  Hint (hidden := true) "3. Compare the resulting circulation with the integral of the constant area density."
  have circulation : squareCirculation rotation = 1 := by
    have edge1 : work (rotation) (fun t => ![t,0,0]) 0 1 = 0 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge2 : work (rotation) (fun t => ![1,t,0]) 0 1 = 1/2 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge3 : work (rotation) (fun t => ![1-t,1,0]) 0 1 = 1/2 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge4 : work (rotation) (fun t => ![0,1-t,0]) 0 1 = 0 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    rw [squareCirculation, edge1, edge2, edge3, edge4]
    norm_num
  constructor
  · rw [circulation]
    norm_num [constant_integral]
  · exact circulation

Conclusion "The rotational boundary integral equals the square’s area 1."
