import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "MultivariableLandscapes"
Level 2
Title "A level set"

Introduction "Objective: Verify that a point lies on a specified level surface.\n\nMathematical prerequisites: Domains, level sets, single-variable limits and continuity. Earlier levels of Multivariable Landscapes.\n\nA level set consists of points where a scalar function has one fixed value. For x²+y²+z²=9, substitute the proposed point into `squarePotential`. This verifies membership in the sphere, rather than a bound on its interior.\n\nWorked example: At (2,0,0), the sum-of-squares field has value 4, so that point belongs to its level set f=4.\n\nExercise: prove the statement below. The hints guide the main steps."

/-- The scalar field x²+y²+z², measuring squared Euclidean distance from the origin. -/
DefinitionDoc VectorCalculus.squarePotential as "squarePotential" in "Calculus notation"
NewDefinition VectorCalculus.squarePotential

/-- Verify that a point lies on a specified level surface. -/
Statement exercise_MultivariableLandscapes_2 : squarePotential ![1,2,2] = 9 := by
  Hint "1. Open the formula for `squarePotential`."
  Hint (hidden := true) "2. Substitute the three coordinates."
  Hint (hidden := true) "3. Add their squares."
  rw [squarePotential]
  norm_num

Conclusion "The point lies on the level surface x²+y²+z²=9."
