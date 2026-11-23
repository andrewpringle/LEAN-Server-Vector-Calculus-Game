import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 1
Title "Hold y fixed"

Introduction "Objective: Compute the first x partial derivative.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals.\n\n`partialX f x y` is `deriv (fun t => f t y) x`: vary x while holding y fixed. Rewrite that definition, remove the constant y² with `deriv_add_const`, and apply the power rule. A partial derivative here is a scalar rate, distinct from the total derivative linear map.\n\nWorked example: For f(x,y)=x³+y, holding y fixed gives the x partial 3x². The added y is constant in this derivative.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Adding a constant to a scalar function does not change its derivative. -/
TheoremDoc deriv_add_const as "deriv_add_const" in "Calculus"
NewTheorem deriv_add_const
/-- Vary the first real argument and hold the second fixed: deriv (fun t => f t y) x. -/
DefinitionDoc VectorCalculus.partialX as "partialX" in "Calculus notation"
NewDefinition VectorCalculus.partialX

/-- Compute the first x partial derivative. -/
Statement exercise_PartialDerivativeLab_1 (x y : ℝ) : partialX (fun s t => s^2 + t^2) x y = 2*x := by
  Hint "1. Open `partialX`."
  Hint (hidden := true) "2. Remove the term that is constant in the varying coordinate."
  Hint (hidden := true) "3. Apply `deriv_pow_field`, then simplify the numerical exponent."
  rw [partialX, deriv_add_const, deriv_pow_field]
  norm_num

Conclusion "Holding y fixed gives the x partial 2x."
