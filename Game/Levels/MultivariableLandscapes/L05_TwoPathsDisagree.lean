import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 5
Title "Two paths disagree"

Introduction "Objective: Disprove a common limit by uniqueness along two paths.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity. Earlier levels of Multivariable Landscapes.\n\nFor f=xy/(x²+y²), the horizontal and diagonal paths approach the punctured origin. `PuncturedLimit` and `PathLimit` keep those punctured limits precise. Prove each path has a constant value away from zero. A hypothetical multivariable limit must restrict to both paths; uniqueness would force its value to be both 0 and 1/2. `rw [not_exists]` rewrites the claim as: every proposed limit fails. You can then introduce an arbitrary limit value and its claimed property.\n\nExercise: prove the statement below."

/-- A punctured multivariable limit restricts to the diagonal path. -/
TheoremDoc VectorCalculus.limit_diagonal as "limit_diagonal" in "Calculus"
/-- A punctured multivariable limit restricts to the horizontal path. -/
TheoremDoc VectorCalculus.limit_horizontal as "limit_horizontal" in "Calculus"
/-- A function constant for all nonzero parameters has that punctured limit. -/
TheoremDoc VectorCalculus.path_limit_of_values as "path_limit_of_values" in "Calculus"
/-- Real path limits are unique. -/
TheoremDoc VectorCalculus.path_limit_unique as "path_limit_unique" in "Calculus"
/-- The nonzero part of the diagonal path is constantly one half. -/
TheoremDoc VectorCalculus.ratio_diagonal as "ratio_diagonal" in "Calculus"
/-- The horizontal path is constantly zero. -/
TheoremDoc VectorCalculus.ratio_horizontal as "ratio_horizontal" in "Calculus"
/-- There is no witness satisfying P exactly when every proposed witness fails. Rewrite with this equivalence, then introduce a proposed witness and its claimed property. -/
TheoremDoc not_exists as "not_exists" in "Calculus"
NewTheorem VectorCalculus.limit_diagonal VectorCalculus.limit_horizontal VectorCalculus.path_limit_of_values VectorCalculus.path_limit_unique VectorCalculus.ratio_diagonal VectorCalculus.ratio_horizontal not_exists
/-- A scalar path limit excludes its zero parameter. -/
DefinitionDoc VectorCalculus.PathLimit as "PathLimit" in "Calculus notation"
/-- A readable name for the punctured multivariable limit at the origin. -/
DefinitionDoc VectorCalculus.PuncturedLimit as "PuncturedLimit" in "Calculus notation"
/-- The field xy/(x²+y²). Its value at the origin does not repair its different limiting values along two paths. -/
DefinitionDoc VectorCalculus.pathRatio as "pathRatio" in "Calculus notation"
NewDefinition VectorCalculus.PathLimit VectorCalculus.PuncturedLimit VectorCalculus.pathRatio

/-- Disprove a common limit by uniqueness along two paths. -/
Statement exercise_MultivariableLandscapes_5 : ¬ ∃ L : ℝ, PuncturedLimit pathRatio L := by
  Hint "1. Rewrite with `not_exists`, then use `intro L assumed` to consider an arbitrary proposed limit."
  Hint (hidden := true) "2. Use `path_limit_of_values` with `ratio_horizontal` and `ratio_diagonal` to establish the two path limits."
  Hint (hidden := true) "3. Compare each with the restriction of `assumed` using `path_limit_unique`; the resulting real equations contradict one another."
  rw [not_exists]
  intro L assumed
  have horizontal : PathLimit (fun t => pathRatio ![t,0,0]) 0 := by
    apply path_limit_of_values
    intro t ht
    rw [ratio_horizontal]
  have diagonal : PathLimit (fun t => pathRatio ![t,t,0]) (1/2) := by
    apply path_limit_of_values
    intro t ht
    rw [ratio_diagonal t ht]
  have first : (0 : ℝ) = L := path_limit_unique horizontal (limit_horizontal assumed)
  have second : (1/2 : ℝ) = L := path_limit_unique diagonal (limit_diagonal assumed)
  linarith

Conclusion "The two punctured paths force incompatible limit values, so no multivariable limit exists."
