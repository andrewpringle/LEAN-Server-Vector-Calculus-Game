import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 2
Title "A weighted wire"

Introduction "Objective: Evaluate a scalar line integral with arc-length weight.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Earlier levels of Path Integral Trails.\n\nA scalar line integral multiplies the scalar density by speed. For this unit-speed wire, the density along the path is t and the speed is 1. Prove the resulting integrand first, replace it in `scalarLineIntegral`, then perform the ordinary integral. Arc-length weight is always nonnegative on the increasing parameter interval.\n\nWorked example: A constant scalar density 1 on a path of speed 2, for 0≤t≤3, gives scalar line integral ∫₀³2 dt=6.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Integrate scalar density along a curve, multiplied by Euclidean speed. Increasing bounds give arc-length weighting. -/
DefinitionDoc VectorCalculus.scalarLineIntegral as "scalarLineIntegral" in "Calculus notation"
NewDefinition VectorCalculus.scalarLineIntegral

/-- Evaluate a scalar line integral with arc-length weight.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * scalarLineIntegral (fun p => p 0) (fun t : ℝ => (![t, 0, 0] : Vec)) 0 2 = (2 : ℝ) * 2 := by
  have established := exercise_PathIntegralTrails_2
  rw [established]
``` -/
TheoremDoc exercise_PathIntegralTrails_2 as "exercise_PathIntegralTrails_2" in "[anonymous]"

/-- Evaluate a scalar line integral with arc-length weight. -/
Statement exercise_PathIntegralTrails_2 : scalarLineIntegral (fun p => p 0) (fun t => ![t,0,0]) 0 2 = 2 := by
  Hint "1. Compute the product of density along the path and speed."
  Hint (hidden := true) "2. Name that product as the scalar integrand t."
  Hint (hidden := true) "3. Rewrite the line integral and use `integral_id`."
  have integrand (t : ℝ) : (fun p : Vec => p 0) ![t,0,0] * speed (fun s => ![s,0,0]) t = t := by
    rw [speed, velocity_components]
    norm_num [length, lengthSq, dot]
  rw [scalarLineIntegral, integral_values integrand, integral_id]
  norm_num

Conclusion "The scalar line integral includes the speed weight and has value 2."
