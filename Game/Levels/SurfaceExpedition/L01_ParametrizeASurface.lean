import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SurfaceExpedition"
Level 1
Title "Parametrize a surface"

Introduction "Objective: Verify that a patch lies in a specified surface.\n\nMathematical prerequisites: Cross products; partial derivatives; double integration.\n\nA surface parametrization has two independent parameters. `patch u v` maps (u,v) to (u,v,0), placing every point in the horizontal plane. Read its height and two planar coordinates directly. The parameter rectangle used later fixes the actual bounded patch.\n\nWorked example: For s(u,v)=(u,v,u+v), substituting (1,2) gives (1,2,3). A surface uses two parameter inputs.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- The horizontal parametrization (u,v,0). On the unit parameter square it gives an upward-oriented square patch. -/
DefinitionDoc VectorCalculus.patch as "patch" in "Calculus notation"
NewDefinition VectorCalculus.patch

/-- Verify that a patch lies in a specified surface. -/
Statement exercise_SurfaceExpedition_1 (u v : ℝ) : (patch u v) 2 = 0 ∧ (patch u v) 0 = u ∧ (patch u v) 1 = v := by
  Hint "1. Separate the height and the two planar coordinates."
  Hint (hidden := true) "2. Read the explicit formula for `patch`."
  Hint (hidden := true) "3. Each coordinate identity follows by `rfl`."
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

Conclusion "The two-parameter map lies in the horizontal plane and retains its planar coordinates."
