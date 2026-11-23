import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-! Coordinate calculus for the game. Derivatives are Mathlib derivatives, and all
integrals are Bochner interval integrals. `Vec` retains the original game's
representation; its Pi norm is NOT used as a Euclidean length. -/
noncomputable section
namespace VectorCalculus

abbrev Vec := Fin 3 → ℝ
abbrev PlaneFunction := ℝ → ℝ → ℝ
abbrev ScalarField := Vec → ℝ
abbrev Field := Vec → Vec

def dot (u v : Vec) : ℝ := u 0 * v 0 + u 1 * v 1 + u 2 * v 2
def lengthSq (v : Vec) : ℝ := dot v v
def length (v : Vec) : ℝ := Real.sqrt (lengthSq v)
def cross (u v : Vec) : Vec :=
  ![u 1 * v 2 - u 2 * v 1, u 2 * v 0 - u 0 * v 2, u 0 * v 1 - u 1 * v 0]
def projection (v n : Vec) : Vec := (dot v n / lengthSq n) • n
def onPlane (n p q : Vec) : Prop := dot n (q - p) = 0
def onLine (p v q : Vec) : Prop := ∃ t : ℝ, q = p + t • v
def planeDistance (n p q : Vec) : ℝ := |dot n (q - p)| / length n

def partialX (f : PlaneFunction) (x y : ℝ) : ℝ := deriv (fun t => f t y) x
def partialY (f : PlaneFunction) (x y : ℝ) : ℝ := deriv (fun t => f x t) y
def coordPartial (f : ScalarField) (p : Vec) (i : Fin 3) : ℝ :=
  deriv (fun t => f (Function.update p i t)) (p i)
def gradient (f : ScalarField) (p : Vec) : Vec := fun i => coordPartial f p i
def divergence (F : Field) (p : Vec) : ℝ :=
  coordPartial (fun q => F q 0) p 0 + coordPartial (fun q => F q 1) p 1 +
    coordPartial (fun q => F q 2) p 2
def curl (F : Field) (p : Vec) : Vec :=
  ![coordPartial (fun q => F q 2) p 1 - coordPartial (fun q => F q 1) p 2,
    coordPartial (fun q => F q 0) p 2 - coordPartial (fun q => F q 2) p 0,
    coordPartial (fun q => F q 1) p 0 - coordPartial (fun q => F q 0) p 1]

def velocity (c : ℝ → Vec) (t : ℝ) : Vec := fun i => deriv (fun s => c s i) t
def speed (c : ℝ → Vec) (t : ℝ) : ℝ := length (velocity c t)
def arcLength (c : ℝ → Vec) (a b : ℝ) : ℝ := ∫ t in a..b, speed c t
def unitTangent (c : ℝ → Vec) (t : ℝ) : Vec := (1 / speed c t) • velocity c t
def curvature (c : ℝ → Vec) (t : ℝ) : ℝ :=
  length (cross (velocity c t) (velocity (velocity c) t)) / speed c t ^ 3
def scalarLineIntegral (f : ScalarField) (c : ℝ → Vec) (a b : ℝ) : ℝ :=
  ∫ t in a..b, f (c t) * speed c t
def work (F : Field) (c : ℝ → Vec) (a b : ℝ) : ℝ :=
  ∫ t in a..b, dot (F (c t)) (velocity c t)
def directional (f : ScalarField) (p u : Vec) : ℝ := fderiv ℝ f p u
def jacobian (F : Field) (p : Vec) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => coordPartial (fun q => F q i) p j

def surfaceNormal (s : ℝ → ℝ → Vec) (u v : ℝ) : Vec :=
  cross (velocity (fun t => s t v) u) (velocity (s u) v)
def surfaceIntegral (f : ScalarField) (s : ℝ → ℝ → Vec) (a b c d : ℝ) : ℝ :=
  ∫ u in a..b, ∫ v in c..d, f (s u v) * length (surfaceNormal s u v)
def surfaceFlux (F : Field) (s : ℝ → ℝ → Vec) (a b c d : ℝ) : ℝ :=
  ∫ u in a..b, ∫ v in c..d, dot (F (s u v)) (surfaceNormal s u v)

def circle (t : ℝ) : Vec := ![Real.cos t, Real.sin t, 0]
def helix (t : ℝ) : Vec := ![Real.cos t, Real.sin t, t]
def patch (u v : ℝ) : Vec := ![u, v, 0]
def liftedPatch (u v : ℝ) : Vec := ![u, v, u * (1-u) * v * (1-v)]
def rotation (p : Vec) : Vec := ![-p 1 / 2, p 0 / 2, 0]
def radial (p : Vec) : Vec := p
def squarePotential (p : Vec) : ℝ := p 0 ^ 2 + p 1 ^ 2 + p 2 ^ 2

/-! Small reusable facts prove infrastructure, not individual level answers. -/
theorem lengthSq_nonneg (v : Vec) : 0 ≤ lengthSq v := by
  unfold lengthSq dot
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem dot_cross_left (u v : Vec) : dot u (cross u v) = 0 := by
  simp [dot, cross]
  ring

theorem dot_cross_right (u v : Vec) : dot v (cross u v) = 0 := by
  simp [dot, cross]
  ring

theorem work_eq_endpoint (F : Field) (f : ScalarField) (c : ℝ → Vec) (a b : ℝ)
    (hchain : ∀ t ∈ Set.uIcc a b,
      HasDerivAt (fun s => f (c s)) (dot (F (c t)) (velocity c t)) t)
    (hint : IntervalIntegrable (fun t => dot (F (c t)) (velocity c t))
      MeasureTheory.volume a b) :
    work F c a b = f (c b) - f (c a) := by
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt hchain hint

theorem reverse_integral (g : ℝ → ℝ) (a b : ℝ) :
    (∫ t in b..a, g t) = -(∫ t in a..b, g t) := by
  exact intervalIntegral.integral_symm a b

end VectorCalculus
