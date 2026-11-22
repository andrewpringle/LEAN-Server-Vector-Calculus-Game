import Game.Metadata
import Mathlib.Basic.Real.Basic
import Mathlib.Algebra.Group.Pi.Basic

World "Vectors"
Level 1
Title "Adding the zero vector"

TacticDoc funext

TheoremDoc zero_add as "zero_add" in "Vectors"

Introduction "
A three-dimensional vector is represented by `Fin 3 → ℝ`.
This assigns a real number to each of the three coordinates.

To prove two vectors equal, compare their coordinates.
"

Statement (v : Fin 3 → ℝ) :
  (0 : Fin 3 → ℝ) + v = v := by
  Hint "Use `funext` to reduce the goal to proving the equality of each coordinate."
  funext i
  Hint "Use `zero_add` to prove the equality of each coordinate."
  exact zero_add (v i)


NewTactic funext exact
NewTheorem zero_add

Conclusion "
You have now proven that adding the zero vector to any vector `v` results in `v` itself.
This is a fundamental property of vector addition in three-dimensional space."
