import GameApi

/-- Close a definitional equality.

### Worked usage example

Read the third coordinate of a new vector. Coordinates are numbered from zero.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (![8, 4, -2] : Vec) 2 = -2 := by
  rfl
``` -/
TacticDoc «rfl» insert "rfl"

/-- Finish a goal with a proof of its statement.

### Worked usage example

Use a hypothesis whose type is exactly the current goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) (h : x ≤ 4) : x ≤ 4 := by
  exact h
``` -/
TacticDoc «exact»

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

/-- Rewrite using proved equalities.

### Worked usage example

Replace equal vectors inside a dot product.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (u v w : Vec) (h : u = v) : dot u w = dot v w := by
  rw [h]
``` -/
TacticDoc «rw» insert "rw [$,]"

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
TacticDoc «have» insert "have $_ : $+ := by $;"

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

/-- Simplify using elementary identities and the explicitly supplied definitions.

### Worked usage example

Simplify a standard identity without calculating a particular value of x.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) : x + 0 = x := by
  simp
``` -/
TacticDoc «simp»

/-- Check numerical coordinate arithmetic after expanding the relevant definitions.

### Worked usage example

Check an explicit real-number calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) + 3 * 4 = 14 := by
  norm_num
``` -/
TacticDoc «norm_num»

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

/-- Solve linear equations or inequalities arising from a plane equation.

### Worked usage example

Combine linear equations to eliminate y and determine x.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x y : ℝ) (hsum : x + y = 5) (hy : y = 2) : x = 3 := by
  linarith
``` -/
TacticDoc «linarith»

/-- Check polynomial identities, including the tangent-plane approximation error.

### Worked usage example

Expand and cancel polynomial terms; this example uses a different offset from the tangent-plane exercise.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example (x : ℝ) : (x + 3)^2 - (x^2 + 6*x) = 9 := by
  ring
``` -/
TacticDoc «ring»

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
