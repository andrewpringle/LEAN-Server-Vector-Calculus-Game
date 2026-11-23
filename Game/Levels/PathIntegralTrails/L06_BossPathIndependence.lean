import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "PathIntegralTrails"
Level 6
Title "Boss: path independence"

Introduction "Objective: Use a potential to compare two paths and compute their common work.\n\nMathematical prerequisites: Regular parametrized curves; vector fields; the fundamental theorem of calculus. Earlier levels of Path Integral Trails.\n\nFor potential φ=x, the endpoint rule `work_first_coordinate` is proved from the fundamental theorem with the stated path regularity and derivative-integrability hypotheses. Apply it to each path. Their shared start and finish then force equal work, and the first equality gives its value as final x minus initial x. This proves path independence for the specified conservative field.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Endpoint evaluation for the potential x, with explicit regularity and integrability. -/
TheoremDoc VectorCalculus.work_first_coordinate as "work_first_coordinate" in "Calculus"
NewTheorem VectorCalculus.work_first_coordinate
/-- A real function is integrable over the interval between its two endpoints. This analytic hypothesis justifies splitting and endpoint evaluation rules. -/
DefinitionDoc IntervalIntegrable as "IntervalIntegrable" in "Calculus notation"
NewDefinition IntervalIntegrable

/-- Use a potential to compare two paths and compute their common work. -/
Statement exercise_PathIntegralTrails_6 (c d : ℝ → Vec) (h0 : c 0 = d 0) (h1 : c 1 = d 1) (hc : RegularPath c 0 1) (hd : RegularPath d 0 1) (hic : IntervalIntegrable (fun t => deriv (fun s => c s 0) t) volume 0 1) (hid : IntervalIntegrable (fun t => deriv (fun s => d s 0) t) volume 0 1) : work (fun _ => ![1,0,0]) c 0 1 = c 1 0-c 0 0 ∧ work (fun _ => ![1,0,0]) c 0 1 = work (fun _ => ![1,0,0]) d 0 1 := by
  Hint "1. Apply the first-coordinate endpoint rule to each path separately."
  Hint (hidden := true) "2. Keep the resulting work-value identities as named facts."
  Hint (hidden := true) "3. Rewrite the two values using the shared endpoints."
  have first := work_first_coordinate c 0 1 hc hic
  have second := work_first_coordinate d 0 1 hd hid
  constructor
  · exact first
  · rw [first, second, h0, h1]

Conclusion "The two paths have equal work because their potential endpoint values coincide."
