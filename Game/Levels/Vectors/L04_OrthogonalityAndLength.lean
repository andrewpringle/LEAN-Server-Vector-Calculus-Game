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

/-- Split a conjunction or construct a structured proof.

### Worked usage example

Prove the two parts of a conjunction in separate branches.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (p : Vec) (hx : p 0 = 2) (hy : p 1 = 7) : p 0 = 2 ∧ p 1 = 7 := by
  constructor
  · exact hx
  · exact hy
``` -/
TacticDoc «constructor»
NewTactic «constructor»
/-- Squared Euclidean length: dot v v. No square root is needed for unit-vector and orthogonality calculations. -/
DefinitionDoc VectorCalculus.lengthSq as "lengthSq" in "Calculus notation"
NewDefinition VectorCalculus.lengthSq

/-- Check perpendicularity and a squared Euclidean length.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * dot (![1, 1, 0] : Vec) (![1, -1, 0] : Vec) = (2 : ℝ) * 0 := by
  have established := exercise_Vectors_4.left
  rw [established]
``` -/
TheoremDoc exercise_Vectors_4 as "exercise_Vectors_4" in "[anonymous]"

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
