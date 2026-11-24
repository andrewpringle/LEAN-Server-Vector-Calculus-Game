import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "TripleIntegralCaverns"
Level 2
Title "Bounds for a solid"

Introduction "Objective: Express a sloping-roof solid with explicit bounds.\n\nMathematical prerequisites: Double integrals; solid bounds; density and moments. Earlier levels of Triple Integral Caverns.\n\nThe solid has roof z=x, with 0≤z≤x≤1 and 0≤y≤1. Translate between the expanded bounds and the shorter nested description. As with triangular regions, x≥0 follows from 0≤z≤x. Read and assemble the inequalities explicitly; the task is choosing valid bounds for a solid.\n\nWorked example: For a roof z≤y with z≥0, the inequality y≥0 follows. A solid description must also state both bounds on the independent horizontal coordinate.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Express a sloping-roof solid with explicit bounds.

This is an example of reusing a completed-level result in a different goal. You cannot use this theorem while proving its own level.

### Worked usage example

Reverse an equivalence with `.symm`. This is a lemma applied to an existing proof, rather than an additional tactic.

Examples use the namespaces and notation opened in the calculus levels.

```lean
example : ∀ (x y z : ℝ), 0 ≤ z ∧ z ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ↔ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ z ∧ z ≤ x := by
  intro x y z
  have established := exercise_TripleIntegralCaverns_2 x y z
  exact established.symm
``` -/
TheoremDoc exercise_TripleIntegralCaverns_2 as "exercise_TripleIntegralCaverns_2" in "[anonymous]"

/-- Express a sloping-roof solid with explicit bounds. -/
Statement exercise_TripleIntegralCaverns_2 (x y z : ℝ) : (0≤x ∧ x≤1 ∧ 0≤y ∧ y≤1 ∧ 0≤z ∧ z≤x) ↔ (0≤z ∧ z≤x ∧ x≤1 ∧ 0≤y ∧ y≤1) := by
  Hint "1. Prove both implications separately."
  Hint (hidden := true) "2. Reorder the listed bounds using conjunction selectors."
  Hint (hidden := true) "3. Recover x≥0 by transitivity of 0≤z and z≤x."
  constructor
  · intro b
    constructor
    · exact b.2.2.2.2.1
    · constructor
      · exact b.2.2.2.2.2
      · constructor
        · exact b.2.1
        · constructor
          · exact b.2.2.1
          · exact b.2.2.2.1
  · intro b
    constructor
    · exact le_trans b.1 b.2.1
    · constructor
      · exact b.2.2.1
      · constructor
        · exact b.2.2.2.1
        · constructor
          · exact b.2.2.2.2
          · constructor
            · exact b.1
            · exact b.2.1

Conclusion "The two descriptions specify the same sloping-roof solid."
