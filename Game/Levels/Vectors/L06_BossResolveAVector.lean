import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 6
Title "Boss: resolve a vector"

Introduction "Objective: Compute a projection and show its remainder is orthogonal.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space. Earlier levels of Vector Workshop.\n\nProject v=(3,1,2) onto the nonzero direction n=(1,1,0). Its squared length is 2, so the projection coefficient (v·n)/(n·n) is 4/2. Name the resulting vector equality with `have`, then reuse it when calculating the remainder. The challenge combines coordinate comparison, dot products, and projection; no new tactic is needed.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Projection of v onto n: (dot v n / lengthSq n) times n. The geometric formula requires a nonzero direction n. -/
DefinitionDoc VectorCalculus.projection as "projection" in "Calculus notation"
NewDefinition VectorCalculus.projection

/-- Compute a projection and show its remainder is orthogonal.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) • projection (![3, 1, 2] : Vec) (![1, 1, 0] : Vec) = (2 : ℝ) • (![2, 2, 0] : Vec) := by
  have established := exercise_Vectors_6.left
  rw [established]
``` -/
TheoremDoc exercise_Vectors_6 as "exercise_Vectors_6" in "[anonymous]"

/-- Compute a projection and show its remainder is orthogonal. -/
Statement exercise_Vectors_6 : projection ![3, 1, 2] ![1, 1, 0] = (![2, 2, 0] : Vec) ∧ dot (![3, 1, 2] - projection ![3, 1, 2] ![1, 1, 0]) ![1, 1, 0] = 0 := by
  Hint "1. First prove and name the projected vector using `vector_eq`."
  Hint (hidden := true) "2. Expand `projection`, `lengthSq`, and `dot` in its three components."
  Hint (hidden := true) "3. Reuse the named equality in the remainder, then calculate its dot product."
  have projected : projection ![3,1,2] ![1,1,0] = (![2,2,0] : Vec) := by
    apply vector_eq
    · norm_num [projection, lengthSq, dot]
    · norm_num [projection, lengthSq, dot]
    · norm_num [projection, lengthSq, dot]
  constructor
  · exact projected
  · rw [projected, dot]
    norm_num

Conclusion "The projection is (2,2,0); the remainder is orthogonal to (1,1,0)."
