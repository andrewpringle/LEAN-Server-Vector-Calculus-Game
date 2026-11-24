import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GradientMountain"
Level 3
Title "Along a parametrized path"

Introduction "Objective: Apply the scalar chain rule to a composite along a path.\n\nMathematical prerequisites: Partial derivatives; unit directions; chain rule and matrices. Earlier levels of Gradient Mountain.\n\nFor the composite (t²)², evaluate the derivative of the outer square at the inner value t². Name the two scalar derivative facts. `derivative_chain` multiplies them, and `derivative_value` lets you finish by proving the product equals the requested polynomial. This keeps the chain-rule choice separate from algebra. The named arguments `f := ...` and `g := ...` specify the outer and inner functions explicitly so Lean need not infer a function from one of its values.\n\nExercise: prove the statement below."

/-- Chain rule stated as a derivative equality; both differentiability facts are required.

### Worked usage example

Compose a cube with a square. The two power-rule facts provide the required differentiability assumptions.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : HasDerivAt (fun s : ℝ => (s^2)^3) ((3*(t^2)^2)*(2*t)) t := by
  apply derivative_chain (f := fun s : ℝ => s^3) (g := fun s : ℝ => s^2) (a := 3*(t^2)^2) (b := 2*t)
  · have h := hasDerivAt_pow 3 (t^2)
    norm_num at h
    exact h
  · have h := hasDerivAt_pow 2 t
    norm_num at h
    exact h
``` -/
TheoremDoc VectorCalculus.derivative_chain as "derivative_chain" in "Calculus"
/-- Replace the displayed derivative value by an algebraically equal value.

### Worked usage example

Change the displayed derivative value only after proving the two expressions are equal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (f : ℝ → ℝ) (a t : ℝ) (h : HasDerivAt f a t) : HasDerivAt f (a+0) t := by
  apply derivative_value h
  ring
``` -/
TheoremDoc VectorCalculus.derivative_value as "derivative_value" in "Calculus"
/-- Power rule with differentiability included: hasDerivAt_pow n t gives derivative n*t^(n-1) of the nth power at t.

### Worked usage example

The power rule supplies differentiability and its value together. norm_num at h simplifies the proved statement.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (t : ℝ) : HasDerivAt (fun s : ℝ => s^3) (3*t^2) t := by
  have h := hasDerivAt_pow 3 t
  norm_num at h
  exact h
``` -/
TheoremDoc hasDerivAt_pow as "hasDerivAt_pow" in "Calculus"
NewTheorem VectorCalculus.derivative_chain VectorCalculus.derivative_value hasDerivAt_pow
/-- HasDerivAt f a t means f is differentiable at t with derivative a. It states existence and the value together. -/
DefinitionDoc HasDerivAt as "HasDerivAt" in "Calculus notation"
NewDefinition HasDerivAt

/-- Apply the scalar chain rule to a composite along a path.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Evaluate the established derivative formula at parameter two, simplifying its numerical value.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : HasDerivAt (fun s : ℝ => (s^2)^2) 32 2 := by
  have h := exercise_GradientMountain_3 2
  norm_num at h
  exact h
``` -/
TheoremDoc exercise_GradientMountain_3 as "exercise_GradientMountain_3" in "[anonymous]"

/-- Apply the scalar chain rule to a composite along a path. -/
Statement exercise_GradientMountain_3 (t : ℝ) : HasDerivAt (fun s : ℝ => (s^2)^2) (4*t^3) t := by
  Hint "1. Name the outer square derivative at t² and the inner square derivative at t."
  Hint (hidden := true) "2. Combine them with `derivative_chain`."
  Hint (hidden := true) "3. Use `derivative_value`, then `ring`, to obtain 4t³."
  have outer : HasDerivAt (fun s : ℝ => s^2) (2*(t^2)) (t^2) := by
    have rule := hasDerivAt_pow 2 (t^2)
    norm_num at rule
    exact rule
  have innerValue : HasDerivAt (fun s : ℝ => s^2) (2*t) t := by
    have rule := hasDerivAt_pow 2 t
    norm_num at rule
    exact rule
  apply derivative_value (derivative_chain (f := fun s : ℝ => s^2) (g := fun s : ℝ => s^2) outer innerValue)
  ring

Conclusion "The composite has derivative 4t³ by the chain rule."
