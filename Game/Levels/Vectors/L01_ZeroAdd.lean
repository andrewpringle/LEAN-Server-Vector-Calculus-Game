import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 1
Title "Coordinates"

Introduction "Objective: Construct a vector and extract its components.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space.\n\n`![a,b,c]` is a spatial vector, with coordinates numbered 0, 1, and 2. Here index 1 selects the middle entry. The type `ℝ` means real numbers; `Vec` keeps the same three-coordinate representation throughout the game. Lean can read a specified coordinate directly, so the familiar `rfl` finishes this first calculation.\n\nWorked example: `(![5,6,7] : Vec) 0 = 5` follows by `rfl`: index 0 selects the first entry.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Apply a lemma to the current goal. -/
TacticDoc «apply»
/-- Finish a goal with a proof of its statement. -/
TacticDoc «exact»
/-- Name an intermediate mathematical fact. -/
TacticDoc «have»
/-- Introduce a hypothesis or a universally quantified variable. -/
TacticDoc «intro»
/-- Choose the first candidate in the Lagrange-system case split. -/
TacticDoc «left»
/-- Close a definitional equality. -/
TacticDoc «rfl»
/-- Choose the second candidate in the Lagrange-system case split. -/
TacticDoc «right»
/-- Rewrite using proved equalities. -/
TacticDoc «rw»
/-- Supply a parameter witnessing membership in a parametric line. -/
TacticDoc «use»
NewTactic «apply» «exact» «have» «intro» «left» «rfl» «right» «rw» «use»
/-- The keyword in belongs to interval-integral notation; it is not a tactic. -/
TacticDoc «in»
NewHiddenTactic «in»
/-- A spatial real vector with coordinates 0, 1, and 2. Write ![x,y,z] and read its coordinates with v 0, v 1, v 2. -/
DefinitionDoc VectorCalculus.Vec as "Vec" in "Calculus notation"
NewDefinition VectorCalculus.Vec

/-- Construct a vector and extract its components. -/
Statement exercise_Vectors_1 : (![2, -1, 3] : Vec) 1 = -1 := by
  Hint "1. Which entry has index 1?"
  Hint (hidden := true) "2. The selected entry is -1 on both sides."
  Hint (hidden := true) "3. Use `rfl`."
  rfl

Conclusion "The second component of the vector is -1."
