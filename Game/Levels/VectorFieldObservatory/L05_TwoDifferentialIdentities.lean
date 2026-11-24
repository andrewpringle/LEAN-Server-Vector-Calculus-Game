import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "VectorFieldObservatory"
Level 5
Title "Two differential identities"

Introduction "Objective: Verify curl-of-gradient and divergence-of-curl for explicit smooth fields.\n\nMathematical prerequisites: Gradients, partial derivatives, and three-dimensional vectors. Earlier levels of Vector Field Observatory.\n\nFirst compute the constant gradient of x and the constant curl of the rotational field. The rules `curl_congr` and `divergence_congr` allow replacement of equal fields. Derivatives of constant components then give zero. These are explicit smooth examples of the differential identities, not an assumption that mixed partials commute without regularity.\n\nExercise: prove the statement below."

/-- Equal vector fields have equal curls.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {F G : VectorCalculus.Field}, (∀ (p : Vec), F p = G p) → ∀ (p : Vec), (2 : ℝ) • curl F p = (2 : ℝ) • curl G p := by
  intro F G h p
  have established := curl_congr h p
  rw [established]
``` -/
TheoremDoc VectorCalculus.curl_congr as "curl_congr" in "Calculus"
/-- Equal vector fields have equal divergences.

### Worked usage example

Use the established equality to evaluate twice the quantity. Rewriting replaces the known expression inside a larger calculation.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ {F G : VectorCalculus.Field},
  (∀ (p : Vec), F p = G p) → ∀ (p : Vec), (2 : ℝ) * divergence F p = (2 : ℝ) * divergence G p := by
  intro F G h p
  have established := divergence_congr h p
  rw [established]
``` -/
TheoremDoc VectorCalculus.divergence_congr as "divergence_congr" in "Calculus"
NewTheorem VectorCalculus.curl_congr VectorCalculus.divergence_congr

/-- Verify curl-of-gradient and divergence-of-curl for explicit smooth fields.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Scale both vectors by two, using the established vector equality inside the new goal.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (p : Vec), (2 : ℝ) • curl (gradient fun q => q 0) p = (2 : ℝ) • 0 := by
  intro p
  have established := (exercise_VectorFieldObservatory_5 p).left
  rw [established]
``` -/
TheoremDoc exercise_VectorFieldObservatory_5 as "exercise_VectorFieldObservatory_5" in "[anonymous]"

/-- Verify curl-of-gradient and divergence-of-curl for explicit smooth fields. -/
Statement exercise_VectorFieldObservatory_5 (p : Vec) : curl (gradient (fun q => q 0)) p = (0 : Vec) ∧ divergence (curl rotation) p = 0 := by
  Hint "1. Name the gradient of x and the curl of the rotational field."
  Hint (hidden := true) "2. Replace the corresponding fields using the congruence rules."
  Hint (hidden := true) "3. Every remaining partial derivative is a constant derivative."
  have grad (q : Vec) : gradient (fun p => p 0) q = (![1,0,0] : Vec) := by
    rw [gradient_components]
    apply vector_eq
    · norm_num [partial_coordinate]
    · norm_num [partial_coordinate]
    · norm_num [partial_coordinate]
  have rotationCurl (q : Vec) : curl rotation q = (![0,0,1] : Vec) := by
    rw [curl]
    apply vector_eq
    · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
    · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
    · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
  constructor
  · rw [curl_congr grad]
    apply vector_eq
    · norm_num [curl, partial_constant]
    · norm_num [curl, partial_constant]
    · norm_num [curl, partial_constant]
  · rw [divergence_congr rotationCurl, divergence]
    norm_num [partial_constant]

Conclusion "Both differential identities hold for the stated explicit smooth examples."
