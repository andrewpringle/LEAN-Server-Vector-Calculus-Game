import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 5
Title "A paraboloid and its traces"

Introduction "Objective: Recognize an elliptic paraboloid and compute two traces.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations. Earlier levels of Space Explorer.\n\nThe surface z=x²+y² is an elliptic paraboloid. Setting y=0 gives a parabola; setting z=1 gives a circle. `simp` removes routine identities such as 0²=0. It is useful after choosing the mathematical substitution. `eq_comm` states that an equality can be read in either direction.\n\nNew tools unlocked here:\n\n`simp`: Simplify using elementary identities and the explicitly supplied definitions.\n\nExercise: prove the statement below."

/-- Simplify using elementary identities and the explicitly supplied definitions. -/
TacticDoc «simp»
NewTactic «simp»
/-- An equality may be read in either direction: a=b is equivalent to b=a. -/
TheoremDoc eq_comm as "eq_comm" in "Calculus"
NewTheorem eq_comm

/-- Recognize an elliptic paraboloid and compute two traces. -/
Statement exercise_SpaceExplorer_5 (x y z : ℝ) : (z = x^2 + (0:ℝ)^2 ↔ z = x^2) ∧ ((1:ℝ) = x^2 + y^2 ↔ x^2 + y^2 = 1) := by
  Hint "1. Separate the two trace statements."
  Hint (hidden := true) "2. The first trace simplifies because the omitted coordinate is zero."
  Hint (hidden := true) "3. For the second trace, use the symmetry of equality, `eq_comm`."
  constructor
  · simp
  · exact eq_comm

Conclusion "The two substitutions produce a parabolic trace and a circular trace."
