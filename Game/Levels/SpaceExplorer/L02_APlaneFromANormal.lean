import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 2
Title "A plane from a normal"

Introduction "Objective: Verify a plane equation from its point-normal definition.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Earlier levels of Space Explorer.\n\nA point q lies in the plane through p with normal n when n·(q-p)=0. The normal (0,0,2) is nonzero. The symbol `↔` asks for both directions of an equivalence: use `constructor`, then `intro h` in each direction. After expanding the plane equation, `linarith` combines linear real equations; here it turns 2(q₂-3)=0 into q₂=3.\n\nWorked example: With normal (0,0,1) and base height 5, the point-normal equation is q₂-5=0, equivalent to q₂=5. A scaled nonzero normal describes the same plane.\n\nNew tools unlocked here:\n\n`linarith`: Solve linear equations or inequalities arising from a plane equation.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Solve linear equations or inequalities arising from a plane equation. -/
TacticDoc «linarith»
NewTactic «linarith»
/-- Point-normal plane equation: dot n (q-p) = 0. A nonzero normal gives a genuine plane. -/
DefinitionDoc VectorCalculus.onPlane as "onPlane" in "Calculus notation"
NewDefinition VectorCalculus.onPlane

/-- Verify a plane equation from its point-normal definition. -/
Statement exercise_SpaceExplorer_2 (q : Vec) : onPlane ![0, 0, 2] ![0, 0, 3] q ↔ q 2 = 3 := by
  Hint "1. Use `constructor` and introduce the hypothesis in each direction."
  Hint (hidden := true) "2. In the forward direction, use `norm_num [onPlane, dot] at h`, then `linarith`."
  Hint (hidden := true) "3. In the reverse direction, substitute the given coordinate with `norm_num [onPlane, dot, h]`."
  constructor
  · intro h
    norm_num [onPlane, dot] at h
    linarith
  · intro h
    norm_num [onPlane, dot, h]

Conclusion "The point-normal equation describes precisely the plane z=3."
