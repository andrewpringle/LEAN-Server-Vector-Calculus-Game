import Game.Metadata
import Game.Rules

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

World "StokesSummit"
Level 6
Title "Boss: choose a simpler surface"

Introduction "Objective: Justify replacing a graph by a planar patch with the same oriented boundary.\n\nMathematical prerequisites: Curl; positively oriented boundaries; parametrized surface flux. Earlier levels of Stokes Summit.\n\nThe raised polynomial graph has exactly the same four oriented boundary traces as the flat patch. Prove those trace equalities first. The graph-normal rule `normal_graph` has vertical component 1, and this field has vertical unit curl, so both flux integrands equal 1. Together with the proved flat-patch Stokes family, this justifies the simpler-surface calculation in this concrete case; it does not assume a general surface-independence theorem.\n\nExercise: prove the statement below. Combine earlier methods and justify every hypothesis."

/-- Graph normals have vertical component one, without assuming a unit normal. -/
TheoremDoc VectorCalculus.normal_graph as "normal_graph" in "Calculus"
NewTheorem VectorCalculus.normal_graph
/-- The graph (u,v,u(1-u)v(1-v)) on the unit parameter square. Its height vanishes on all four boundary edges. -/
DefinitionDoc VectorCalculus.liftedPatch as "liftedPatch" in "Calculus notation"
NewDefinition VectorCalculus.liftedPatch

/-- Justify replacing a graph by a planar patch with the same oriented boundary. -/
Statement exercise_StokesSummit_6 : (∀ t : ℝ, liftedPatch t 0 = patch t 0 ∧ liftedPatch 1 t = patch 1 t ∧ liftedPatch (1-t) 1 = patch (1-t) 1 ∧ liftedPatch 0 (1-t) = patch 0 (1-t)) ∧ surfaceFlux (curl (fun p => ![0,p 0,0])) liftedPatch 0 1 0 1 = surfaceFlux (curl (fun p => ![0,p 0,0])) patch 0 1 0 1 := by
  Hint "1. Verify all four boundary traces, including their decreasing parameter directions."
  Hint (hidden := true) "2. Use `normal_graph` to identify the vertical area-vector component."
  Hint (hidden := true) "3. Evaluate both curl fluxes and compare their values."
  constructor
  · intro t
    constructor
    · apply vector_eq
      · norm_num [liftedPatch, patch]
      · norm_num [liftedPatch, patch]
      · norm_num [liftedPatch, patch]
    · constructor
      · apply vector_eq
        · norm_num [liftedPatch, patch]
        · norm_num [liftedPatch, patch]
        · norm_num [liftedPatch, patch]
      · constructor
        · apply vector_eq
          · norm_num [liftedPatch, patch]
          · norm_num [liftedPatch, patch]
          · norm_num [liftedPatch, patch]
        · apply vector_eq
          · norm_num [liftedPatch, patch]
          · norm_num [liftedPatch, patch]
          · norm_num [liftedPatch, patch]
  · have raisedVertical (u v : ℝ) : (surfaceNormal liftedPatch u v) 2 = 1 := by
      have coordinates (s t : ℝ) : liftedPatch s t = (![s,t,s*(1-s)*t*(1-t)] : Vec) := by rfl
      rw [normal_congr coordinates, normal_graph]
      norm_num
    have flatVertical (u v : ℝ) : (surfaceNormal patch u v) 2 = 1 := by
      have coordinates (s t : ℝ) : patch s t = (![s,t,0] : Vec) := by rfl
      rw [normal_congr coordinates, normal_components]
      norm_num [partialX, partialY, cross]
    have raised : surfaceFlux (curl (fun p => ![0,p 0,0])) liftedPatch 0 1 0 1 = 1 := by
      norm_num [surfaceFlux, curl, partial_coordinate, partial_constant, dot, raisedVertical]
    have flat : surfaceFlux (curl (fun p => ![0,p 0,0])) patch 0 1 0 1 = 1 := by
      norm_num [surfaceFlux, curl, partial_coordinate, partial_constant, dot, flatVertical]
    rw [raised, flat]

Conclusion "The raised and flat patches have the same oriented boundary and equal computed curl flux in this concrete case."
