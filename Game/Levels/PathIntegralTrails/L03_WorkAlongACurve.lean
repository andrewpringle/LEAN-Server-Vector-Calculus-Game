import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 3
Title "Work along a curve"

Introduction "Objective: Integrate a vector field dotted with the curve velocity.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Earlier levels of Path Integral Trails.\n\nWork integrates F(c(t))·c′(t). Substitute the path into the field, compute velocity, and take the dot product before integrating. This integrand has an orientation-sensitive velocity, unlike the speed factor in a scalar line integral.\n\nExercise: prove the statement below."

/-- Integrate field-along-path dotted with velocity. This signed integral depends on path orientation. -/
DefinitionDoc VectorCalculus.work as "work" in "Calculus notation"
NewDefinition VectorCalculus.work

/-- Integrate a vector field dotted with the curve velocity.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * work (fun p => (![p 0, 0, 0] : Vec)) (fun t : ℝ => (![t, 0, 0] : Vec)) 0 2 = (2 : ℝ) * 2 := by
  have established := exercise_PathIntegralTrails_3
  rw [established]
``` -/
TheoremDoc exercise_PathIntegralTrails_3 as "exercise_PathIntegralTrails_3" in "[anonymous]"

/-- Integrate a vector field dotted with the curve velocity. -/
Statement exercise_PathIntegralTrails_3 : work (fun p => ![p 0,0,0]) (fun t => ![t,0,0]) 0 2 = 2 := by
  Hint "1. Compute the field on the path and the component velocity."
  Hint (hidden := true) "2. Name their dot product as the integrand t."
  Hint (hidden := true) "3. Rewrite `work` with that formula and integrate."
  have integrand (t : ℝ) : dot ((fun p : Vec => ![p 0,0,0]) ![t,0,0]) (velocity (fun s => ![s,0,0]) t) = t := by
    rw [velocity_components, dot]
    norm_num
  rw [work, integral_values integrand, integral_id]
  norm_num

Conclusion "The field-velocity work integral has value 2."
