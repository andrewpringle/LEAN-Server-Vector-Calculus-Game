import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 4
Title "Arc length of a segment"

Introduction "Objective: Integrate the speed of a regular curve on ordered bounds.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration. Earlier levels of Curve Navigator.\n\nFor increasing bounds, arc length integrates the nonnegative speed. This segment is regular and has constant speed 1. Prove that speed formula first. `integral_values` replaces an integrand by a pointwise equal function, and `constant_integral` integrates a constant as interval length times value.\n\nExercise: prove the statement below."

/-- A constant integral is its value times the interval's signed length. -/
TheoremDoc VectorCalculus.constant_integral as "constant_integral" in "Calculus"
/-- Pointwise equal integrands have equal interval integrals. -/
TheoremDoc VectorCalculus.integral_values as "integral_values" in "Calculus"
NewTheorem VectorCalculus.constant_integral VectorCalculus.integral_values
/-- Integrate Euclidean speed over the parameter interval. Geometric arc length uses increasing bounds. -/
DefinitionDoc VectorCalculus.arcLength as "arcLength" in "Calculus notation"
NewDefinition VectorCalculus.arcLength

/-- Integrate the speed of a regular curve on ordered bounds. -/
Statement exercise_CurveNavigator_4 : arcLength (fun t => ![t,0,0]) 0 3 = 3 := by
  Hint "1. Prove that speed equals 1 for every parameter value."
  Hint (hidden := true) "2. Rewrite `arcLength`, then replace its integrand with `integral_values unitSpeed`."
  Hint (hidden := true) "3. Apply `constant_integral` and evaluate the interval length."
  have unitSpeed (t : ℝ) : speed (fun s => ![s,0,0]) t = 1 := by
    rw [speed, velocity_components]
    norm_num [length, lengthSq, dot]
  rw [arcLength, integral_values unitSpeed, constant_integral]
  norm_num

Conclusion "The segment has constant unit speed and arc length 3."
