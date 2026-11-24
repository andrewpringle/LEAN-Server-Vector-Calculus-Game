import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 3
Title "Curl through a patch"

Introduction "Objective: Compute the curl flux integrand in Stokes’ formula.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Earlier levels of Stokes Summit.\n\nStokes uses curl F dotted with the parameter normal. Compute the normal and the cross-coordinate derivatives for F=(0,x,0). Its curl points upward, so the dot product is 1. Keeping the normal vector rather than only its length preserves the orientation sign.\n\nExercise: prove the statement below."


/-- Compute the curl flux integrand in Stokes’ formula.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (u v : ℝ), (2 : ℝ) * dot (curl (fun p => (![0, p 0, 0] : Vec)) (patch u v)) (surfaceNormal patch u v) = (2 : ℝ) * 1 := by
  intro u v
  have established := exercise_StokesSummit_3 u v
  rw [established]
``` -/
TheoremDoc exercise_StokesSummit_3 as "exercise_StokesSummit_3" in "[anonymous]"

/-- Compute the curl flux integrand in Stokes’ formula. -/
Statement exercise_StokesSummit_3 (u v : ℝ) : dot (curl (fun p => ![0,p 0,0]) (patch u v)) (surfaceNormal patch u v) = 1 := by
  Hint "1. Find the parameter normal."
  Hint (hidden := true) "2. Open the curl formula and use the coordinate partial rules."
  Hint (hidden := true) "3. Take the oriented dot product."
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  rw [normal, curl, dot]
  norm_num [partial_coordinate, partial_constant]

Conclusion "The curl dotted with the oriented patch normal equals 1."
