import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 5
Title "Apply the endpoint theorem"

Introduction "Objective: Use an established fundamental theorem for line integrals.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Earlier levels of Path Integral Trails.\n\n`RegularPath` records differentiability of every coordinate along the interval. `PotentialAlong` states the derivative of the potential along the curve equals F·c′, and `WorkIntegrable` records integrability of that actual integrand. These names abbreviate the established derivative and integral conditions; none assumes the desired work equality. Apply the endpoint theorem and supply its two analytic hypotheses.\n\nExercise: prove the statement below."

/-- The fundamental theorem along a path: if the potential derivative is the work integrand and that integrand is interval integrable, work equals the potential endpoint difference. -/
TheoremDoc VectorCalculus.work_eq_endpoint as "work_eq_endpoint" in "Calculus"
NewTheorem VectorCalculus.work_eq_endpoint
/-- The potential differentiated along the path equals the work integrand. -/
DefinitionDoc VectorCalculus.PotentialAlong as "PotentialAlong" in "Calculus notation"
/-- Curve regularity in the coordinate representation. -/
DefinitionDoc VectorCalculus.RegularPath as "RegularPath" in "Calculus notation"
/-- Integrability of the actual work integrand on the ordered or reversed interval. -/
DefinitionDoc VectorCalculus.WorkIntegrable as "WorkIntegrable" in "Calculus notation"
NewDefinition VectorCalculus.PotentialAlong VectorCalculus.RegularPath VectorCalculus.WorkIntegrable

/-- Use an established fundamental theorem for line integrals. -/
Statement exercise_PathIntegralTrails_5 (F : Field) (f : ScalarField) (c : ℝ → Vec) (a b : ℝ) (hcurve : RegularPath c a b) (hc : PotentialAlong F f c a b) (hi : WorkIntegrable F c a b) : work F c a b = f (c b)-f (c a) := by
  Hint "1. Identify which assumption gives the derivative of the potential along the path."
  Hint (hidden := true) "2. Apply `work_eq_endpoint`."
  Hint (hidden := true) "3. Supply `hc` and `hi` separately."
  apply work_eq_endpoint
  · exact hc
  · exact hi

Conclusion "The derivative-along-path and integrability hypotheses justify endpoint evaluation."
