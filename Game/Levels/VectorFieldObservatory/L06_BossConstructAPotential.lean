import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 6
Title "Boss: construct a potential"

Introduction "Objective: Supply a potential and verify it globally.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Earlier levels of Vector Field Observatory.\n\nConstruct a globally defined potential for (y,x,0) and normalize its value to zero at the origin. Supply the scalar function with `use`, check its value, then calculate its gradient at an arbitrary point. Reuse the product partial rule rather than inferring conservativity from curl alone.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- A scalar field assigns one real value to each spatial point. -/
DefinitionDoc VectorCalculus.ScalarField as "ScalarField" in "Calculus notation"
NewDefinition VectorCalculus.ScalarField

/-- Supply a potential and verify it globally. -/
Statement exercise_VectorFieldObservatory_6 : ∃ f : ScalarField, f ![0,0,0] = 0 ∧ ∀ p, gradient f p = (![p 1,p 0,0] : Vec) := by
  Hint "1. Integrate the first component y with respect to x to propose a potential."
  Hint (hidden := true) "2. Choose the additive constant so the origin value is zero."
  Hint (hidden := true) "3. For an arbitrary point, verify all three gradient components."
  use fun q => q 0*q 1
  constructor
  · norm_num
  · intro p
    rw [gradient_components]
    apply vector_eq
    · norm_num [partial_xy]
    · norm_num [partial_xy]
    · norm_num [partial_xy]

Conclusion "The supplied globally defined potential has the required gradient and normalization."
