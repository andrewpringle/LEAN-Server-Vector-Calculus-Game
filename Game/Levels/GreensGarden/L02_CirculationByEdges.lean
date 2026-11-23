import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 2
Title "Circulation by edges"

Introduction "Objective: Evaluate circulation directly along a closed boundary.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation. Earlier levels of Green’s Garden.\n\nCompute circulation directly by evaluating work on each of the four counterclockwise edges. Only the right edge contributes for F=(0,x,0). Name the four edge values before adding them with `squareCirculation`. This supplies an independent boundary calculation before any use of Green’s theorem.\n\nWorked example: For F=(0,2x,0), the upward right edge x=1 has work integrand 2, giving contribution 2 over its unit parameter interval.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- The derivative of t ↦ a-t is -1, preserving the sign of a reversed parameter. -/
TheoremDoc deriv_const_sub_id as "deriv_const_sub_id" in "Calculus"
NewTheorem deriv_const_sub_id
/-- Counterclockwise circulation on the four edges of the unit square. -/
DefinitionDoc VectorCalculus.squareCirculation as "squareCirculation" in "Calculus notation"
NewDefinition VectorCalculus.squareCirculation

/-- Evaluate circulation directly along a closed boundary. -/
Statement exercise_GreensGarden_2 : squareCirculation (fun p => ![0,p 0,0]) = 1 := by
  Hint "1. Calculate one work integral per oriented edge."
  Hint (hidden := true) "2. The right edge has constant integrand 1; the others contribute zero."
  Hint (hidden := true) "3. Rewrite `squareCirculation` using the four named edge values and add."
  have edge1 : work (fun p => ![0,p 0,0]) (fun t => ![t,0,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge2 : work (fun p => ![0,p 0,0]) (fun t => ![1,t,0]) 0 1 = 1 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge3 : work (fun p => ![0,p 0,0]) (fun t => ![1-t,1,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge4 : work (fun p => ![0,p 0,0]) (fun t => ![0,1-t,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  rw [squareCirculation, edge1, edge2, edge3, edge4]
  norm_num

Conclusion "The four independent edge calculations give circulation 1."
