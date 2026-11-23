import Game.Calculus

/-! Audited special cases of the integral theorems. These are deliberately
restricted families, proved by evaluating actual derivatives and integrals.
No general Green/Stokes/Gauss theorem is asserted by these definitions. -/
noncomputable section
namespace VectorCalculus
open intervalIntegral

/-- Counterclockwise circulation on the four edges of the unit square. -/
def squareCirculation (F : Field) : ℝ :=
  work F (fun t => ![t,0,0]) 0 1 +
  work F (fun t => ![1,t,0]) 0 1 +
  work F (fun t => ![1-t,1,0]) 0 1 +
  work F (fun t => ![0,1-t,0]) 0 1

/-- Outward planar flux, using the outward unit conormal of each unit-speed edge. -/
def squareOutwardFlux (F : Field) : ℝ :=
  (∫ t in (0:ℝ)..1, dot (F ![t,0,0]) ![0,-1,0]) +
  (∫ t in (0:ℝ)..1, dot (F ![1,t,0]) ![1,0,0]) +
  (∫ t in (0:ℝ)..1, dot (F ![1-t,1,0]) ![0,1,0]) +
  (∫ t in (0:ℝ)..1, dot (F ![0,1-t,0]) ![-1,0,0])

/-- Six square parametrizations whose parameter cross products point outward. -/
def cubeFlux (F : Field) : ℝ :=
  surfaceFlux F (fun u v => ![1,u,v]) 0 1 0 1 +
  surfaceFlux F (fun u v => ![0,v,u]) 0 1 0 1 +
  surfaceFlux F (fun u v => ![v,1,u]) 0 1 0 1 +
  surfaceFlux F (fun u v => ![u,0,v]) 0 1 0 1 +
  surfaceFlux F (fun u v => ![u,v,1]) 0 1 0 1 +
  surfaceFlux F (fun u v => ![v,u,0]) 0 1 0 1

/-- Green's circulation identity for a linear shear on the unit square. -/
theorem green_shear (k : ℝ) :
    squareCirculation (fun p => ![0,k*p 0,0]) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1,
        (curl (fun p => ![0,k*p 0,0]) ![x,y,0]) 2 := by
  simp [squareCirculation, work, velocity, dot, curl, coordPartial,
    Function.update, deriv_const_sub_id, deriv_const_mul_id]

/-- Stokes' identity for a linear shear on an upward unit-square patch. -/
theorem stokes_shear_patch (k : ℝ) :
    squareCirculation (fun p => ![0,k*p 0,0]) =
      surfaceFlux (curl (fun p => ![0,k*p 0,0])) patch 0 1 0 1 := by
  rw [green_shear]
  simp [surfaceFlux, surfaceNormal, patch, velocity, cross, dot, curl,
    coordPartial, Function.update, deriv_const_mul_id]

/-- Gauss' identity for diagonal linear fields on the outward unit cube. -/
theorem gauss_diagonal (a b c : ℝ) :
    cubeFlux (fun p => ![a*p 0,b*p 1,c*p 2]) =
      ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1,
        divergence (fun p => ![a*p 0,b*p 1,c*p 2]) ![x,y,z] := by
  simp [cubeFlux, surfaceFlux, surfaceNormal, velocity, cross, dot,
    divergence, coordPartial, Function.update, deriv_const_mul_id]

end VectorCalculus
