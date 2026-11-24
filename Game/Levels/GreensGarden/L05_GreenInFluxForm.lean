import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 5
Title "Green in flux form"

Introduction "Objective: Verify outward planar flux equals the divergence integral.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation. Earlier levels of Green’s Garden.\n\nFor F=(x,y,0), compute outward planar flux using the four specified unit conormals, then compute the integral of divergence 2. Right and top edges contribute 1 each; bottom and left contribute zero. Equality of these independent calculations verifies the flux-form Green special case, with outward conormals distinct from boundary tangent directions.\n\nExercise: prove the statement below."

/-- Outward planar flux, using the outward unit conormal of each unit-speed edge. -/
DefinitionDoc VectorCalculus.squareOutwardFlux as "squareOutwardFlux" in "Calculus notation"
NewDefinition VectorCalculus.squareOutwardFlux

/-- Verify outward planar flux equals the divergence integral.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ((2 : ℝ) * squareOutwardFlux fun p => (![p 0, p 1, 0] : Vec)) =
  (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, divergence (fun p => (![p 0, p 1, 0] : Vec)) (![x, y, 0] : Vec) := by
  have established := exercise_GreensGarden_5
  rw [established]
``` -/
TheoremDoc exercise_GreensGarden_5 as "exercise_GreensGarden_5" in "[anonymous]"

/-- Verify outward planar flux equals the divergence integral. -/
Statement exercise_GreensGarden_5 : squareOutwardFlux (fun p => ![p 0,p 1,0]) = (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, divergence (fun p => ![p 0,p 1,0]) ![x,y,0]) := by
  Hint "1. Evaluate the outward edge sum as one named boundary value."
  Hint (hidden := true) "2. Compute matching-coordinate derivatives for the interior value."
  Hint (hidden := true) "3. Rewrite both sides using those independent calculations."
  have boundary : squareOutwardFlux (fun p => ![p 0,p 1,0]) = 2 := by
    rw [squareOutwardFlux]
    norm_num [dot]
  have insideValue : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, divergence (fun p => ![p 0,p 1,0]) ![x,y,0]) = 2 := by
    norm_num [divergence, partial_coordinate, partial_constant]
  rw [boundary, insideValue]

Conclusion "Independent outward-flux and divergence calculations verify this flux-form Green special case."
