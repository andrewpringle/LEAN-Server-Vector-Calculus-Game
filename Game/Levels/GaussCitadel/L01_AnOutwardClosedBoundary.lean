import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "GaussCitadel"
Level 1
Title "An outward closed boundary"

Introduction "Objective: Verify outward orientation on all six cube faces.\n\nMathematical prerequisites: Divergence; oriented surface flux; triple integrals; integral theorem special cases.\n\nA closed cube has six faces, and every face must point outward. The parameter order differs between opposite faces. Calculate all six cross-product normals: +x, -x, +y, -y, +z, -z. The same six parametrizations occur in `cubeFlux`, so the closed-boundary orientation is fully explicit.\n\nWorked example: On the top plane z=2 of a box, the parameter order (s,t,2) produces an upward normal, away from its interior. Opposite faces require opposite normals.\n\nExercise: prove the statement below. The hints guide the main steps."


/-- Verify outward orientation on all six cube faces. -/
Statement exercise_GaussCitadel_1 (u v : ℝ) : surfaceNormal (fun s t => ![1,s,t]) u v = (![1,0,0] : Vec) ∧ surfaceNormal (fun s t => ![0,t,s]) u v = (![-1,0,0] : Vec) ∧ surfaceNormal (fun s t => ![t,1,s]) u v = (![0,1,0] : Vec) ∧ surfaceNormal (fun s t => ![s,0,t]) u v = (![0,-1,0] : Vec) ∧ surfaceNormal (fun s t => ![s,t,1]) u v = (![0,0,1] : Vec) ∧ surfaceNormal (fun s t => ![t,s,0]) u v = (![0,0,-1] : Vec) := by
  Hint "1. Separate the six face-normal statements."
  Hint (hidden := true) "2. Use `normal_components` for each parametrization."
  Hint (hidden := true) "3. Check that the normal points away from the cube interior on that face."
  constructor
  · rw [normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  · constructor
    · rw [normal_components]
      apply vector_eq
      · norm_num [partialX, partialY, cross]
      · norm_num [partialX, partialY, cross]
      · norm_num [partialX, partialY, cross]
    · constructor
      · rw [normal_components]
        apply vector_eq
        · norm_num [partialX, partialY, cross]
        · norm_num [partialX, partialY, cross]
        · norm_num [partialX, partialY, cross]
      · constructor
        · rw [normal_components]
          apply vector_eq
          · norm_num [partialX, partialY, cross]
          · norm_num [partialX, partialY, cross]
          · norm_num [partialX, partialY, cross]
        · constructor
          · rw [normal_components]
            apply vector_eq
            · norm_num [partialX, partialY, cross]
            · norm_num [partialX, partialY, cross]
            · norm_num [partialX, partialY, cross]
          · rw [normal_components]
            apply vector_eq
            · norm_num [partialX, partialY, cross]
            · norm_num [partialX, partialY, cross]
            · norm_num [partialX, partialY, cross]

Conclusion "All six face normals point outward, including each pair of opposite directions."
