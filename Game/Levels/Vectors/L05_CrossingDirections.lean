import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "Vectors"
Level 5
Title "Crossing directions"

Introduction "Objective: Compute a cross product and verify perpendicularity.\n\nMathematical prerequisites: Real arithmetic; vectors in three-dimensional space. Earlier levels of Vector Workshop.\n\nThe right-hand rule fixes the order in a cross product. Compute its three components using `vector_eq` and the definition `cross`. For perpendicularity, apply the proved rule `dot_cross_left`: any vector is perpendicular to its cross product with another vector.\n\nExercise: prove the statement below."

/-- A vector is perpendicular to its cross product with another vector: dot u (cross u v) = 0. -/
TheoremDoc VectorCalculus.dot_cross_left as "dot_cross_left" in "Calculus"
NewTheorem VectorCalculus.dot_cross_left
/-- The right-handed cross product in coordinate order. Its direction changes when the two input vectors are exchanged. -/
DefinitionDoc VectorCalculus.cross as "cross" in "Calculus notation"
NewDefinition VectorCalculus.cross

/-- Compute a cross product and verify perpendicularity. -/
Statement exercise_Vectors_5 : cross ![1, 0, 0] ![0, 1, 0] = (![0, 0, 1] : Vec) ∧ dot ![1, 0, 0] (cross ![1, 0, 0] ![0, 1, 0]) = 0 := by
  Hint "1. Split the cross-product calculation from the perpendicularity claim."
  Hint (hidden := true) "2. Use `vector_eq`; `norm_num [cross]` checks each component."
  Hint (hidden := true) "3. For the second goal, apply `dot_cross_left`."
  constructor
  · apply vector_eq
    · norm_num [cross]
    · norm_num [cross]
    · norm_num [cross]
  · apply dot_cross_left

Conclusion "The cross product is (0,0,1) and is perpendicular to its first input."
