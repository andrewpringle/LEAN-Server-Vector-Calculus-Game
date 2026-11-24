import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 4
Title "The boundary calculation"

Introduction "Objective: Evaluate circulation with the orientation induced by the surface.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Earlier levels of Stokes Summit.\n\nEvaluate boundary circulation directly for F=(0,2x,0). Use the same four oriented edges as in Green’s Garden. Only the upward right edge contributes, with value 2. This independently checks the boundary side before invoking the surface theorem.\n\nExercise: prove the statement below."


/-- Evaluate circulation with the orientation induced by the surface.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) = (2 : ℝ) * 2 := by
  have established := exercise_StokesSummit_4
  rw [established]
``` -/
TheoremDoc exercise_StokesSummit_4 as "exercise_StokesSummit_4" in "[anonymous]"

/-- Evaluate circulation with the orientation induced by the surface. -/
Statement exercise_StokesSummit_4 : squareCirculation (fun p => ![0,2*p 0,0]) = 2 := by
  Hint "1. Compute the four edge work integrals."
  Hint (hidden := true) "2. Retain the top and left reversal signs in their velocities."
  Hint (hidden := true) "3. Add the four named values using `squareCirculation`."
  have edge1 : work (fun p => ![0,2*p 0,0]) (fun t => ![t,0,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge2 : work (fun p => ![0,2*p 0,0]) (fun t => ![1,t,0]) 0 1 = 2 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge3 : work (fun p => ![0,2*p 0,0]) (fun t => ![1-t,1,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge4 : work (fun p => ![0,2*p 0,0]) (fun t => ![0,1-t,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  rw [squareCirculation, edge1, edge2, edge3, edge4]
  norm_num

Conclusion "Direct boundary circulation equals 2."
