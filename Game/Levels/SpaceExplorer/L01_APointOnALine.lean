import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "SpaceExplorer"
Level 1
Title "A point on a line"

Introduction "Objective: Supply a parameter witnessing line membership.\n\nMathematical prerequisites: Vector Workshop; parametric lines, normals, and quadratic equations.\n\n`onLine p v q` says that q=p+t v for some real parameter t. As in an existence proof in NNG, `use 2` supplies a witness. Then compare the three coordinates with the vector rule from Vector Workshop. A correct parameter must satisfy every coordinate.\n\nWorked example: The line p=(0,0,0)+t(1,0,0) contains (3,0,0), witnessed by t=3.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Line membership means there is a real parameter t for which q = p + t times v. Supply a witness with use. -/
DefinitionDoc VectorCalculus.onLine as "onLine" in "Calculus notation"
NewDefinition VectorCalculus.onLine

/-- Supply a parameter witnessing line membership.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

A known point on a line can witness that the line is nonempty.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∃ q : Vec, onLine ![1,0,2] ![1,2,-1] q := by
  use ![3,4,0]
  exact exercise_SpaceExplorer_1
``` -/
TheoremDoc exercise_SpaceExplorer_1 as "exercise_SpaceExplorer_1" in "[anonymous]"

/-- Supply a parameter witnessing line membership. -/
Statement exercise_SpaceExplorer_1 : onLine ![1, 0, 2] ![1, 2, -1] ![3, 4, 0] := by
  Hint "1. Solve the first coordinate for the parameter."
  Hint (hidden := true) "2. Supply the witness with `use 2`."
  Hint (hidden := true) "3. Apply `vector_eq` and check all three coordinates."
  use 2
  apply vector_eq
  · norm_num
  · norm_num
  · norm_num

Conclusion "Parameter 2 places the proposed point on the line."
