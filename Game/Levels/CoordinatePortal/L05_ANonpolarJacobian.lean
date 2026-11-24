import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "CoordinatePortal"
Level 5
Title "A nonpolar Jacobian"

Introduction "Objective: Compute a determinant for a linear coordinate transformation.\n\nMathematical prerequisites: Multiple integrals; determinants; trigonometric identities. Earlier levels of Coordinate Portal.\n\nThe map T(u,v)=(2u,-3v) has derivative matrix diag(2,-3). Derive its entries from the coordinate partials before taking the determinant. Name the signed determinant and reuse it for the absolute determinant. The negative sign records orientation reversal; area scaling uses its positive magnitude.\n\nExercise: prove the statement below."


/-- Compute a determinant for a linear coordinate transformation.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * (planarJacobian (fun u x => (2 : ℝ) * u) (fun x v => -3 * v) 0 0).det = (2 : ℝ) * -6 := by
  have established := exercise_CoordinatePortal_5.left
  rw [established]
``` -/
TheoremDoc exercise_CoordinatePortal_5 as "exercise_CoordinatePortal_5" in "[anonymous]"

/-- Compute a determinant for a linear coordinate transformation. -/
Statement exercise_CoordinatePortal_5 : Matrix.det (planarJacobian (fun u _ => 2*u) (fun _ v => -3*v) 0 0) = -6 ∧ |Matrix.det (planarJacobian (fun u _ => 2*u) (fun _ v => -3*v) 0 0)| = 6 := by
  Hint "1. Compute the derivative entries and the 2×2 determinant."
  Hint (hidden := true) "2. Name the signed determinant -6."
  Hint (hidden := true) "3. Reuse that equality when taking the absolute value."
  have determinant : Matrix.det (planarJacobian (fun u _ => 2*u) (fun _ v => -3*v) 0 0) = -6 := by
    norm_num [planarJacobian, partialX, partialY, Matrix.det_fin_two, deriv_const_mul_id]
  constructor
  · exact determinant
  · rw [determinant]
    norm_num

Conclusion "The transformation reverses orientation with signed determinant -6 and area factor 6."
