import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PartialDerivativeLab"
Level 2
Title "Hold x fixed"

Introduction "Objective: Compute the first y partial derivative.\n\nMathematical prerequisites: Joint continuity; scalar derivatives; planes and normals. Earlier levels of Partial Derivative Lab.\n\nNow hold x fixed and vary y. The same power rule gives 2y, written here as y+y. `ring` proves polynomial identities such as 2y=y+y; it does not decide which variable to differentiate. Use it after applying the calculus rules.\n\nWorked example: For f(x,y)=xy, holding x fixed gives the y partial x. Switching the varying coordinate changes which factor is constant.\n\nNew tools unlocked here:\n\n`ring`: Check polynomial identities, including the tangent-plane approximation error.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Check polynomial identities, including the tangent-plane approximation error. -/
TacticDoc «ring»
NewTactic «ring»
/-- A constant added before a scalar function does not change its derivative. -/
TheoremDoc deriv_const_add as "deriv_const_add" in "Calculus"
NewTheorem deriv_const_add
/-- Hold the first real argument fixed and vary the second: deriv (fun t => f x t) y. -/
DefinitionDoc VectorCalculus.partialY as "partialY" in "Calculus notation"
NewDefinition VectorCalculus.partialY

/-- Compute the first y partial derivative. -/
Statement exercise_PartialDerivativeLab_2 (x y : ℝ) : partialY (fun s t => s^2+t^2) x y = y+y := by
  Hint "1. Open `partialY` and remove the fixed x² term."
  Hint (hidden := true) "2. Apply the power rule to the varying y²."
  Hint (hidden := true) "3. Use `ring` to write the result as y+y."
  rw [partialY, deriv_const_add, deriv_pow_field]
  ring

Conclusion "Holding x fixed gives the y partial y+y, equivalently 2y."
