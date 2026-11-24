import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 2
Title "Polar area factor"

Introduction "Objective: Derive the polar determinant and integrate the unit disk area density.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities. Earlier levels of Coordinate Portal.\n\nBuild the polar Jacobian from the actual partial derivatives of r cos θ and r sin θ, then use the 2×2 determinant rule. The sine-cosine identity simplifies the determinant to r. The assumption r≥0 permits replacing |r| by r. Finally integrate that radial area factor over the standard disk parameter domain. This evaluates the coordinate-side integral, not a general substitution theorem.\n\nWorked example: For T(u,v)=(3u,2v), compute derivative columns (3,0) and (0,2). Their 2×2 determinant is 6, so the area factor is |6|=6.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Join equalities through an intermediate value. apply Eq.trans (b := value) asks for the first and second equality.

### Worked usage example

Use the equality in the opposite direction. Rewriting works inside a goal, including when the known value is on its left.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {α : Type} {a b c : α}, a = b → b = c → c = a := by
  intro α a b c h₁ h₂
  have established := Eq.trans h₁ h₂
  rw [established]
``` -/
TheoremDoc Eq.trans as "trans" in "Calculus"
/-- The 2 by 2 determinant formula: top-left times bottom-right minus top-right times bottom-left.

### Worked usage example

Expand a new two-by-two determinant before doing arithmetic.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : Matrix.det ((!![(3 : ℝ), 1; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ)) = 6 := by
  rw [Matrix.det_fin_two]
  norm_num
``` -/
TheoremDoc Matrix.det_fin_two as "det_fin_two" in "Calculus"
/-- For a nonnegative real a, its absolute value equals a. Supply the nonnegativity proof.

### Worked usage example

Prove the sign before removing the absolute value.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) (hx : 0 ≤ x) : |x + 2| = x + 2 := by
  apply abs_of_nonneg
  linarith
``` -/
TheoremDoc abs_of_nonneg as "abs_of_nonneg" in "Calculus"
NewTheorem Eq.trans Matrix.det_fin_two abs_of_nonneg
/-- The signed determinant of a square matrix. Change-of-variables area and volume use its absolute value. -/
DefinitionDoc Matrix.det as "det" in "Calculus notation"
/-- The real number π. Standard polar and azimuthal angular intervals have length 2π, measured in radians. -/
DefinitionDoc Real.pi as "pi" in "Calculus notation"
/-- The 2 by 2 matrix whose columns are the actual first and second parameter derivatives of a planar map. -/
DefinitionDoc VectorCalculus.planarJacobian as "planarJacobian" in "Calculus notation"
/-- The first polar coordinate function: r cos θ. -/
DefinitionDoc VectorCalculus.polarX as "polarX" in "Calculus notation"
/-- The second polar coordinate function: r sin θ. -/
DefinitionDoc VectorCalculus.polarY as "polarY" in "Calculus notation"
/-- The radial field F(p)=p, pointing directly away from the origin. -/
DefinitionDoc VectorCalculus.radial as "radial" in "Calculus notation"
NewDefinition Matrix.det Real.pi VectorCalculus.planarJacobian VectorCalculus.polarX VectorCalculus.polarY VectorCalculus.radial

/-- Derive the polar determinant and integrate the unit disk area density.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (r t : ℝ), 0 ≤ r → (2 : ℝ) * |(planarJacobian polarX polarY r t).det| = (2 : ℝ) * r := by
  intro r t hr
  have established := (exercise_CoordinatePortal_2 r t hr).left
  rw [established]
``` -/
TheoremDoc exercise_CoordinatePortal_2 as "exercise_CoordinatePortal_2" in "[anonymous]"

/-- Derive the polar determinant and integrate the unit disk area density. -/
Statement exercise_CoordinatePortal_2 (r t : ℝ) (hr : 0≤r) : |Matrix.det (planarJacobian polarX polarY r t)| = r ∧ (∫ t : ℝ in 0..(2*Real.pi), ∫ r : ℝ in 0..1, r) = Real.pi := by
  Hint "1. Compute the four partials and expand the 2×2 determinant."
  Hint (hidden := true) "2. Factor the result as r(sin²θ+cos²θ), then use r≥0 for its absolute value."
  Hint (hidden := true) "3. Integrate r on [0,1], then the resulting constant over [0,2π]."
  have determinant : Matrix.det (planarJacobian polarX polarY r t) = r := by
    norm_num [planarJacobian, polarX, polarY, partialX, partialY, Matrix.det_fin_two, deriv_mul_const_field, deriv_const_mul_field]
    apply Eq.trans (b := r*(Real.sin t^2+Real.cos t^2))
    · ring
    · rw [Real.sin_sq_add_cos_sq]
      ring
  constructor
  · rw [determinant, abs_of_nonneg hr]
  · have radial : (∫ r : ℝ in 0..1, r) = 1/2 := by
      rw [integral_id]
      norm_num
    rw [radial, constant_integral]
    ring

Conclusion "The derived polar determinant has absolute factor r on r≥0, and the coordinate-side area integral is π."
