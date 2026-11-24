import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 3
Title "The dot product"

Introduction "Objective: Evaluate the coordinate formula for an inner product.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space. Earlier levels of Vector Workshop.\n\nThe dot product multiplies matching components and adds the results. `rw [dot]` opens that coordinate formula, just as rewriting opened definitions in the Natural Number Game. Then use the numerical arithmetic tool from the preceding level.\n\nExercise: prove the statement below."

/-- Euclidean dot product: multiply the three matching coordinates and add. Use rw [dot] to display the formula. -/
DefinitionDoc VectorCalculus.dot as "dot" in "Calculus notation"
NewDefinition VectorCalculus.dot

/-- Evaluate the coordinate formula for an inner product.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * dot (![1, 2, -1] : Vec) (![3, 0, 4] : Vec) = (2 : ℝ) * -1 := by
  have established := exercise_Vectors_3
  rw [established]
``` -/
TheoremDoc exercise_Vectors_3 as "exercise_Vectors_3" in "[anonymous]"

/-- Evaluate the coordinate formula for an inner product. -/
Statement exercise_Vectors_3 : dot ![1, 2, -1] ![3, 0, 4] = -1 := by
  Hint "1. Start with the coordinate formula for the dot product."
  Hint (hidden := true) "2. Use `rw [dot]` to expand that formula."
  Hint (hidden := true) "3. Use `norm_num` to check 3 + 0 - 4 = -1."
  rw [dot]
  norm_num

Conclusion "The dot product is 3+0-4=-1."
