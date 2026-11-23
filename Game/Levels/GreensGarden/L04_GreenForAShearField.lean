import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 4
Title "Green for a shear field"

Introduction "Objective: Apply a proved circulation-form Green special case.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation. Earlier levels of Green’s Garden.\n\nApply the established Green circulation identity for the smooth shear family F=(0,kx,0) on the positively oriented unit square. Here k=3. The theorem is a fully proved special case for this family and boundary, not a claim about arbitrary regions or fields. The earlier levels verified both sides directly for k=1.\n\nExercise: prove the statement below."

/-- Green's circulation identity for a linear shear on the unit square. -/
TheoremDoc VectorCalculus.green_shear as "green_shear" in "Calculus"
NewTheorem VectorCalculus.green_shear

/-- Apply a proved circulation-form Green special case. -/
Statement exercise_GreensGarden_4 : squareCirculation (fun p => ![0,3*p 0,0]) = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, (curl (fun p => ![0,3*p 0,0]) ![x,y,0]) 2 := by
  Hint "1. Recognize the field as a member of the shear family."
  Hint (hidden := true) "2. Identify coefficient k=3 and the positive square orientation."
  Hint (hidden := true) "3. Apply `green_shear`."
  apply green_shear

Conclusion "The proved shear-family Green identity applies with coefficient 3 and the stated boundary orientation."
