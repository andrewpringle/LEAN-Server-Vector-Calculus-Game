import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 4
Title "Orthogonality and length"

Introduction "Objective: Check perpendicularity and a squared Euclidean length.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space. Earlier levels of Vector Workshop.\n\nOrthogonal vectors have dot product zero. Squared length is the dot product of a vector with itself. The symbol `∧` asks for both statements: `constructor` splits them into two goals, which you solve under separate bullets. Each calculation then uses a formula you know.\n\nNew tools unlocked here:\n\n`constructor`: Split a conjunction or construct a structured proof.\n\nExercise: prove the statement below."

/-- Split a conjunction or construct a structured proof. -/
TacticDoc «constructor»
NewTactic «constructor»
/-- Squared Euclidean length: dot v v. No square root is needed for unit-vector and orthogonality calculations. -/
DefinitionDoc VectorCalculus.lengthSq as "lengthSq" in "Calculus notation"
NewDefinition VectorCalculus.lengthSq

/-- Check perpendicularity and a squared Euclidean length. -/
Statement exercise_Vectors_4 : dot ![1, 1, 0] ![1, -1, 0] = 0 ∧ lengthSq ![1, 1, 0] = 2 := by
  Hint "1. Use `constructor` to separate orthogonality and squared length."
  Hint (hidden := true) "2. Rewrite the first goal with `dot`."
  Hint (hidden := true) "3. Rewrite the second with `lengthSq` and `dot`, then calculate."
  constructor
  · rw [dot]
    norm_num
  · rw [lengthSq, dot]
    norm_num

Conclusion "The vectors are orthogonal, and the squared length of (1,1,0) is 2."
