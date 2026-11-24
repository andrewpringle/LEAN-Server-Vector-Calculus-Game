import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GreensGarden"
Level 3
Title "The interior integrand"

Introduction "Objective: Compute the matching planar curl integral.\n\nMathematical prerequisites: Planar line integrals; double integrals; positive orientation. Earlier levels of Green’s Garden.\n\nFor the same field, the planar curl integrand is ∂Q/∂x-∂P/∂y=1. Calculate this derivative expression, then integrate it over the square. Its value agrees with the independent edge calculation, verifying the interior side of this example.\n\nExercise: prove the statement below."


/-- Compute the matching planar curl integral.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 = (2 : ℝ) * 1 := by
  have established := exercise_GreensGarden_3
  rw [established]
``` -/
TheoremDoc exercise_GreensGarden_3 as "exercise_GreensGarden_3" in "[anonymous]"

/-- Compute the matching planar curl integral. -/
Statement exercise_GreensGarden_3 : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, (curl (fun p => ![0,p 0,0]) ![x,y,0]) 2) = 1 := by
  Hint "1. Calculate the vertical component of curl at an arbitrary square point."
  Hint (hidden := true) "2. Integrate the resulting constant in y."
  Hint (hidden := true) "3. Replace that inner integral and integrate in x."
  have integrand (x y : ℝ) : (curl (fun p => ![0,p 0,0]) ![x,y,0]) 2 = 1 := by
    rw [curl]
    norm_num [partial_coordinate, partial_constant]
  have innerValue (x : ℝ) : (∫ y : ℝ in 0..1, (curl (fun p => ![0,p 0,0]) ![x,y,0]) 2) = 1 := by
    rw [integral_values (integrand x), constant_integral]
    norm_num
  rw [integral_values innerValue, constant_integral]
  norm_num

Conclusion "The square integral of the planar curl equals 1."
