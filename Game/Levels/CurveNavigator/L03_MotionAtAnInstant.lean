import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CurveNavigator"
Level 3
Title "Motion at an instant"

Introduction "Objective: Calculate velocity, acceleration, and speed at a regular point.\n\nMathematical prerequisites: Vector algebra; single-variable differentiation and integration. Earlier levels of Curve Navigator.\n\nAcceleration is the velocity of the velocity curve. First name the velocity formula for an arbitrary time. `velocity_congr` lets you differentiate a curve after replacing it by a proved equal formula. Speed is the Euclidean length of velocity; it is not another component derivative.\n\nExercise: prove the statement below."

/-- Replacing an equal curve also replaces its component derivatives.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {c d : ℝ → Vec}, (∀ (t : ℝ), c t = d t) → ∀ (t : ℝ), (2 : ℝ) • velocity c t = (2 : ℝ) • velocity d t := by
  intro c d h t
  have established := velocity_congr h t
  rw [established]
``` -/
TheoremDoc VectorCalculus.velocity_congr as "velocity_congr" in "Calculus"
/-- The derivative of t ↦ a*t is the constant a.

### Worked usage example

A line of slope five has derivative five at every parameter.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : deriv (fun s : ℝ => 5*s) t = 5 := by
  exact deriv_const_mul_id 5
``` -/
TheoremDoc deriv_const_mul_id as "deriv_const_mul_id" in "Calculus"
NewTheorem VectorCalculus.velocity_congr deriv_const_mul_id
/-- The Euclidean length of velocity, always nonnegative. -/
DefinitionDoc VectorCalculus.speed as "speed" in "Calculus notation"
NewDefinition VectorCalculus.speed

/-- Calculate velocity, acceleration, and speed at a regular point.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) • velocity (fun s => (![s, s ^ 2, 0] : Vec)) 0 = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  have established := exercise_CurveNavigator_3.left
  rw [established]
``` -/
TheoremDoc exercise_CurveNavigator_3 as "exercise_CurveNavigator_3" in "[anonymous]"

/-- Calculate velocity, acceleration, and speed at a regular point. -/
Statement exercise_CurveNavigator_3 : velocity (fun s => ![s,s^2,0]) 0 = (![1,0,0] : Vec) ∧ velocity (velocity (fun s => ![s,s^2,0])) 0 = (![0,2,0] : Vec) ∧ speed (fun s => ![s,s^2,0]) 0 = 1 := by
  Hint "1. Name the component velocity formula for every time t."
  Hint (hidden := true) "2. Replace the velocity curve using `velocity_congr`, then differentiate again."
  Hint (hidden := true) "3. For speed at zero, rewrite with the named velocity and evaluate its length."
  have vel (t : ℝ) : velocity (fun s => ![s,s^2,0]) t = (![1,2*t,0] : Vec) := by
    rw [velocity_components]
    apply vector_eq
    · norm_num [deriv_pow_field]
    · norm_num [deriv_pow_field]
    · norm_num [deriv_pow_field]
  constructor
  · norm_num [vel]
  · constructor
    · rw [velocity_congr vel, velocity_components]
      apply vector_eq
      · norm_num [deriv_const_mul_id]
      · norm_num [deriv_const_mul_id]
      · norm_num [deriv_const_mul_id]
    · rw [speed, vel 0]
      norm_num [length, lengthSq, dot]

Conclusion "Velocity, acceleration, and Euclidean speed at the chosen instant are verified separately."
