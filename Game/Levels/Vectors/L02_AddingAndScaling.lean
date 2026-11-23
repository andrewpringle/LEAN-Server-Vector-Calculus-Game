import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 2
Title "Adding and scaling"

Introduction "Objective: Compute a linear combination coordinate by coordinate.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space. Earlier levels of Vector Workshop.\n\nAddition and scalar multiplication act on each coordinate. Use `apply vector_eq` to turn one vector equality into three real equalities. The three bullets `·` handle those goals in order. This proved rule lets you compare coordinates without learning how Lean implements finite functions. `norm_num` checks concrete arithmetic; it does not choose the vector operation for you.\n\nWorked example: For u=(2,0,1) and v=(1,1,0), u+v=(3,1,1). After `apply vector_eq`, check the three scalar sums under separate bullets.\n\nNew tools unlocked here:\n\n`norm_num`: Check numerical coordinate arithmetic after expanding the relevant definitions.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- Check numerical coordinate arithmetic after expanding the relevant definitions. -/
TacticDoc «norm_num»
NewTactic «norm_num»
/-- Three component equalities suffice to prove equality of spatial vectors. -/
TheoremDoc VectorCalculus.vector_eq as "vector_eq" in "Calculus"
NewTheorem VectorCalculus.vector_eq

/-- Compute a linear combination coordinate by coordinate. -/
Statement exercise_Vectors_2 : (![1, 2, 0] : Vec) + (2 : ℝ) • ![0, -1, 3] = ![1, 0, 6] := by
  Hint "1. Apply `vector_eq` to compare the three coordinates."
  Hint (hidden := true) "2. Lean now asks for the x, y, and z calculations separately."
  Hint (hidden := true) "3. Use `norm_num` under each of the three bullets."
  apply vector_eq
  · norm_num
  · norm_num
  · norm_num

Conclusion "The vector sum is (1,0,6), verified in all three coordinates."
