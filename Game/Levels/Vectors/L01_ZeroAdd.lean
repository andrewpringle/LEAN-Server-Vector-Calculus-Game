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

/-- Apply a lemma to the current goal.

### Worked usage example

Apply a rule, then supply the premise it requests. Here step is an explicitly given implication.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) (h : x ≤ 4) (step : x ≤ 4 → x ≤ 5) : x ≤ 5 := by
  apply step
  exact h
``` -/
TacticDoc «apply»
/-- Finish a goal with a proof of its statement.

### Worked usage example

Use a hypothesis whose type is exactly the current goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) (h : x ≤ 4) : x ≤ 4 := by
  exact h
``` -/
TacticDoc «exact»
/-- Name an intermediate mathematical fact.

### Worked usage example

Name a useful equality before using it in the goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x y z : ℝ) (hxy : x = y) (hyz : y = z) : x = z := by
  have firstStep : x = y := hxy
  rw [firstStep]
  exact hyz
``` -/
TacticDoc «have»
/-- Introduce a hypothesis or a universally quantified variable.

### Worked usage example

Introduce the parameter before proving an identity that holds for every real number.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ x : ℝ, x = x := by
  intro x
  rfl
``` -/
TacticDoc «intro»
/-- Choose the first candidate in the Lagrange-system case split.

### Worked usage example

Prove the first alternative of a disjunction from the supplied coordinate fact.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (p : Vec) (h : p 0 = 2) : p 0 = 2 ∨ p 0 = 5 := by
  left
  exact h
``` -/
TacticDoc «left»
/-- Close a definitional equality.

### Worked usage example

Read the third coordinate of a new vector. Coordinates are numbered from zero.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (![8, 4, -2] : Vec) 2 = -2 := by
  rfl
``` -/
TacticDoc «rfl»
/-- Choose the second candidate in the Lagrange-system case split.

### Worked usage example

Prove the second alternative when that is the fact you know.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (p : Vec) (h : p 0 = 5) : p 0 = 2 ∨ p 0 = 5 := by
  right
  exact h
``` -/
TacticDoc «right»
/-- Rewrite using proved equalities.

### Worked usage example

Replace equal vectors inside a dot product.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (u v w : Vec) (h : u = v) : dot u w = dot v w := by
  rw [h]
``` -/
TacticDoc «rw»
/-- Supply a parameter witnessing membership in a parametric line.

### Worked usage example

Choose a parameter that makes the requested coordinate equal to five.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∃ t : ℝ, (![t, 3, 0] : Vec) 0 = 5 := by
  use 5
  rfl
``` -/
TacticDoc «use»
NewTactic «apply» «exact» «have» «intro» «left» «rfl» «right» «rw» «use»
/-- The keyword in belongs to interval-integral notation; it is not a tactic. -/
TacticDoc «in»
NewHiddenTactic «in»
/-- A spatial real vector with coordinates 0, 1, and 2. Write ![x,y,z] and read its coordinates with v 0, v 1, v 2. -/
DefinitionDoc VectorCalculus.Vec as "Vec" in "Calculus notation"
NewDefinition VectorCalculus.Vec

/-- Construct a vector and extract its components.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * (![2, -1, 3] : Vec) 1 = (2 : ℝ) * -1 := by
  have established := exercise_Vectors_1
  rw [established]
``` -/
TheoremDoc exercise_Vectors_1 as "exercise_Vectors_1" in "[anonymous]"

/-- Construct a vector and extract its components. -/
Statement exercise_Vectors_1 : (![2, -1, 3] : Vec) 1 = -1 := by
  Hint "1. Which entry has index 1?"
  Hint (hidden := true) "2. The selected entry is -1 on both sides."
  Hint (hidden := true) "3. Use `rfl`."
  rfl

Conclusion "The second component of the vector is -1."
