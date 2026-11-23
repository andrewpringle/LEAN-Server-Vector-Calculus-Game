import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 1
Title "The boundary of a patch"

Introduction "Objective: Determine all four oriented boundary traces of a parametrized patch.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux.\n\nThe four sides of the parameter square give the patch boundary. Traverse them with u increasing on the bottom, v increasing on the right, u decreasing on the top, and v decreasing on the left. Verify all four traces; these are the oriented edge curves used in the square circulation.\n\nWorked example: For a stretched rectangle s(u,v)=(2u,v,0), fixing v=0 gives its bottom edge (2u,0,0). Fix a parameter to obtain each edge.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Determine all four oriented boundary traces of a parametrized patch. -/
Statement exercise_StokesSummit_1 (t : ℝ) : patch t 0 = (![t,0,0] : Vec) ∧ patch 1 t = (![1,t,0] : Vec) ∧ patch (1-t) 1 = (![1-t,1,0] : Vec) ∧ patch 0 (1-t) = (![0,1-t,0] : Vec) := by
  Hint "1. Restrict the parametrization to each side of its square domain."
  Hint (hidden := true) "2. Keep decreasing parameters on the top and left."
  Hint (hidden := true) "3. Separate the four trace equalities and read their coordinates."
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

Conclusion "All four parameter-edge restrictions give the stated oriented boundary traces."
