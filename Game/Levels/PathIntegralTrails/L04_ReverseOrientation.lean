import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 4
Title "Reverse orientation"

Introduction "Objective: Show that reversing oriented integration negates work.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Earlier levels of Path Integral Trails.\n\nReversing the parameter bounds reverses oriented work. Open the two occurrences of `work` and apply the interval-reversal rule `reverse_integral`. This statement concerns the oriented integral; it does not negate a geometric arc length.\n\nExercise: prove the statement below."

/-- Interchanging interval endpoints negates the signed integral of the same integrand.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (g : ℝ → ℝ) (a b : ℝ), (2 : ℝ) * ∫ (t : ℝ) in b..a, g t = (2 : ℝ) * -∫ (t : ℝ) in a..b, g t := by
  intro g a b
  have established := reverse_integral g a b
  rw [established]
``` -/
TheoremDoc VectorCalculus.reverse_integral as "reverse_integral" in "Calculus"
NewTheorem VectorCalculus.reverse_integral
/-- A vector field takes a spatial point and returns a spatial vector. -/
DefinitionDoc VectorCalculus.Field as "Field" in "Calculus notation"
NewDefinition VectorCalculus.Field

/-- Show that reversing oriented integration negates work.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (F : VectorCalculus.Field) (c : ℝ → Vec) (a b : ℝ), (2 : ℝ) * work F c b a = (2 : ℝ) * -work F c a b := by
  intro F c a b
  have established := exercise_PathIntegralTrails_4 F c a b
  rw [established]
``` -/
TheoremDoc exercise_PathIntegralTrails_4 as "exercise_PathIntegralTrails_4" in "[anonymous]"

/-- Show that reversing oriented integration negates work. -/
Statement exercise_PathIntegralTrails_4 (F : Field) (c : ℝ → Vec) (a b : ℝ) : work F c b a = -work F c a b := by
  Hint "1. Open the work definitions on both sides."
  Hint (hidden := true) "2. The integrand is unchanged and the interval bounds are reversed."
  Hint (hidden := true) "3. Apply `reverse_integral`."
  rw [work, work]
  apply reverse_integral

Conclusion "Reversing the parameter bounds negates oriented work."
