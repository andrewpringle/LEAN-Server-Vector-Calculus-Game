import Game

open VectorCalculus MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

-- abs_of_nonneg
example (x : ℝ) (hx : 0 ≤ x) : |x + 2| = x + 2 := by
  apply abs_of_nonneg
  linarith

-- add_nonneg
example (x y : ℝ) (hx : 0 ≤ x) (hy : 0 ≤ y) : 0 ≤ x + y := by
  exact add_nonneg hx hy

-- add_pos_of_nonneg_of_pos
example (y : ℝ) (hy : 0 < y) : 0 < 3 + y := by
  apply add_pos_of_nonneg_of_pos
  · norm_num
  · exact hy

-- add_pos_of_pos_of_nonneg
example (x : ℝ) (hx : 0 < x) : 0 < x + 3 := by
  apply add_pos_of_pos_of_nonneg hx
  norm_num

-- apply
example (x : ℝ) (h : x ≤ 4) (step : x ≤ 4 → x ≤ 5) : x ≤ 5 := by
  apply step
  exact h

-- constructor
example (p : Vec) (hx : p 0 = 2) (hy : p 1 = 7) : p 0 = 2 ∧ p 1 = 7 := by
  constructor
  · exact hx
  · exact hy

-- continuous_apply
example : Continuous (fun p : Vec => p 2) := by
  exact continuous_apply 2

-- deriv_add_const
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => f s + 8) t = deriv f t := by
  rw [deriv_add_const]

-- deriv_const
example (t : ℝ) : deriv (fun _ : ℝ => (9 : ℝ)) t = 0 := by
  exact deriv_const t 9

-- deriv_const_add
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => 8 + f s) t = deriv f t := by
  rw [deriv_const_add]

-- deriv_const_mul_field
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => 7 * f s) t = 7 * deriv f t := by
  rw [deriv_const_mul_field]

-- deriv_const_mul_id
example (t : ℝ) : deriv (fun s : ℝ => 5*s) t = 5 := by
  exact deriv_const_mul_id 5

-- deriv_const_sub_id
example (t : ℝ) : deriv (fun s : ℝ => 8-s) t = -1 := by
  exact deriv_const_sub_id 8

-- deriv_mul_const_field
example (f : ℝ → ℝ) (t : ℝ) : deriv (fun s : ℝ => f s * 5) t = deriv f t * 5 := by
  rw [deriv_mul_const_field]

-- deriv_neg
example (t : ℝ) : deriv (fun s : ℝ => -s) t = -1 := by
  exact deriv_neg t

-- deriv_pow_field
example (t : ℝ) : deriv (fun s : ℝ => s^3) t = 3*t^2 := by
  rw [deriv_pow_field]
  norm_num

-- eq_comm
example (x y : ℝ) : x = y ↔ y = x := by
  exact eq_comm (a := x) (b := y)

-- Eq.trans
example : ∀ {α : Type} {a b c : α}, a = b → b = c → c = a := by
  intro α a b c h₁ h₂
  have established := Eq.trans h₁ h₂
  rw [established]

-- exact
example (x : ℝ) (h : x ≤ 4) : x ≤ 4 := by
  exact h

-- exercise_CoordinatePortal_1
example : ∀ (r t : ℝ), (2 : ℝ) * ((r * Real.cos t) ^ 2 + (r * Real.sin t) ^ 2) = (2 : ℝ) * r ^ 2 := by
  intro r t
  have established := exercise_CoordinatePortal_1 r t
  rw [established]

-- exercise_CoordinatePortal_2
example : ∀ (r t : ℝ), 0 ≤ r → (2 : ℝ) * |(planarJacobian polarX polarY r t).det| = (2 : ℝ) * r := by
  intro r t hr
  have established := (exercise_CoordinatePortal_2 r t hr).left
  rw [established]

-- exercise_CoordinatePortal_3
example : (2 : ℝ) * ∫ (t : ℝ) in 0..(2 : ℝ) * Real.pi, ∫ (r : ℝ) in 0..1, ∫ (z : ℝ) in 0..2, r = (2 : ℝ) * ((2 : ℝ) * Real.pi) := by
  have established := exercise_CoordinatePortal_3
  rw [established]

-- exercise_CoordinatePortal_4
example : (2 : ℝ) * (∫ t : ℝ in 0..(2*Real.pi), ∫ p : ℝ in 0..Real.pi, ∫ r : ℝ in 0..1, r^2*Real.sin p) = 8*Real.pi/3 := by
  rw [exercise_CoordinatePortal_4.2]
  ring

-- exercise_CoordinatePortal_5
example : (2 : ℝ) * (planarJacobian (fun u x => (2 : ℝ) * u) (fun x v => -3 * v) 0 0).det = (2 : ℝ) * -6 := by
  have established := exercise_CoordinatePortal_5.left
  rw [established]

-- exercise_CoordinatePortal_6
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in -3..0, (1 : ℝ) = (2 : ℝ) * ∫ (u : ℝ) (v : ℝ) in 0..1, |(!![2, 0; 0, -3] : Matrix (Fin 2) (Fin 2) ℝ).det| := by
  have established := exercise_CoordinatePortal_6
  rw [established]

-- exercise_CurveNavigator_1
example : (2 : ℝ) • (fun t : ℝ => (![t, t ^ 2, 0] : Vec)) 0 = (2 : ℝ) • (![0, 0, 0] : Vec) := by
  have established := exercise_CurveNavigator_1.left
  rw [established]

-- exercise_CurveNavigator_2
example : ∀ (t : ℝ), (2 : ℝ) • velocity (fun s => (![s, s ^ 2, 0] : Vec)) t = (2 : ℝ) • (![1, (2 : ℝ) * t, 0] : Vec) := by
  intro t
  have established := exercise_CurveNavigator_2 t
  rw [established]

-- exercise_CurveNavigator_3
example : (2 : ℝ) • velocity (fun s => (![s, s ^ 2, 0] : Vec)) 0 = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  have established := exercise_CurveNavigator_3.left
  rw [established]

-- exercise_CurveNavigator_4
example : (2 : ℝ) * arcLength (fun t : ℝ => (![t, 0, 0] : Vec)) 0 3 = (2 : ℝ) * 3 := by
  have established := exercise_CurveNavigator_4
  rw [established]

-- exercise_CurveNavigator_5
example : (2 : ℝ) • unitTangent circle 0 = (2 : ℝ) • (![0, 1, 0] : Vec) := by
  have established := exercise_CurveNavigator_5.left
  rw [established]

-- exercise_CurveNavigator_6
example (t : ℝ) : 2 * lengthSq (velocity helix t) = 4 := by
  rw [(exercise_CurveNavigator_6 t).2.2]
  norm_num

-- exercise_DoubleIntegralValley_1
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..3, (1 : ℝ) = (2 : ℝ) * 6 := by
  have established := exercise_DoubleIntegralValley_1
  rw [established]

-- exercise_DoubleIntegralValley_2
example : ∀ (x y : ℝ), 0 ≤ y ∧ y ≤ x ∧ x ≤ 1 ↔ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ x := by
  intro x y
  have established := exercise_DoubleIntegralValley_2 x y
  exact established.symm

-- exercise_DoubleIntegralValley_3
example : (2 : ℝ) * ∫ (x : ℝ) in 0..1, ∫ (y : ℝ) in 0..x, (1 : ℝ) = (2 : ℝ) * ∫ (y : ℝ) in 0..1, ∫ (x : ℝ) in y..1, (1 : ℝ) := by
  have established := exercise_DoubleIntegralValley_3
  rw [established]

-- exercise_DoubleIntegralValley_4
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..3, (1 : ℝ) = (2 : ℝ) * 6 := by
  have established := exercise_DoubleIntegralValley_4.left
  rw [established]

-- exercise_DoubleIntegralValley_5
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..1, (1 : ℝ) = (2 : ℝ) * 2 := by
  have established := exercise_DoubleIntegralValley_5.left
  rw [established]

-- exercise_DoubleIntegralValley_6
example : (2 : ℝ) * ∫ (x : ℝ) in 0..1, ∫ (y : ℝ) in 0..x, (1 : ℝ) = (2 : ℝ) * (1 / 2) := by
  have established := exercise_DoubleIntegralValley_6.left
  rw [established]

-- exercise_GaussCitadel_1
example : ∀ (u v : ℝ), (2 : ℝ) • surfaceNormal (fun s t => (![1, s, t] : Vec)) u v = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  intro u v
  have established := (exercise_GaussCitadel_1 u v).left
  rw [established]

-- exercise_GaussCitadel_2
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, divergence radial (![x, y, z] : Vec) = (2 : ℝ) * 3 := by
  have established := exercise_GaussCitadel_2
  rw [established]

-- exercise_GaussCitadel_3
example : (2 : ℝ) * cubeFlux radial = (2 : ℝ) * 3 := by
  have established := exercise_GaussCitadel_3
  rw [established]

-- exercise_GaussCitadel_4
example : ((2 : ℝ) * cubeFlux fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) =
  2 *
    ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, divergence (fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) (![x, y, z] : Vec) := by
  have established := exercise_GaussCitadel_4
  rw [established]

-- exercise_GaussCitadel_5
example : ∀ (top : ℝ), (cubeFlux fun p => (![(2 : ℝ) * p 0, 3 * p 1, 4 * p 2] : Vec)) = 5 + top → (2 : ℝ) * top = (2 : ℝ) * 4 := by
  intro top h
  have established := exercise_GaussCitadel_5 top h
  rw [established]

-- exercise_GaussCitadel_6
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) =
  (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 := by
  have established := exercise_GaussCitadel_6.left
  rw [established]

-- exercise_GradientMountain_1
example : ∀ (p : Vec), (2 : ℝ) • gradient (fun q => q 0) p = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  intro p
  have established := exercise_GradientMountain_1 p
  rw [established]

-- exercise_GradientMountain_2
example : ∀ (p u : Vec), lengthSq u = 1 → (2 : ℝ) * directional (fun q => q 0) p u = (2 : ℝ) * u 0 := by
  intro p u hu
  have established := exercise_GradientMountain_2 p u hu
  rw [established]

-- exercise_GradientMountain_3
example : HasDerivAt (fun s : ℝ => (s^2)^2) 32 2 := by
  have h := exercise_GradientMountain_3 2
  norm_num at h
  exact h

-- exercise_GradientMountain_4
example (p : Vec) : (jacobian (fun q => ![q 0,q 1,q 2]) p) 0 2 = 0 := by
  rw [exercise_GradientMountain_4 p]
  norm_num [Matrix.one_apply]

-- exercise_GradientMountain_5
example : ∀ (u : Vec), lengthSq u = 1 → (2 : ℝ) * dot (![3, 4, 0] : Vec) u ≤ (2 : ℝ) * 5 := by
  intro u hu
  have established := exercise_GradientMountain_5 u hu
  linarith [established]

-- exercise_GradientMountain_6
example : ∀ (p v : Vec), p 0 = 2 → v 0 = 0 → (2 : ℝ) * (p + v) 0 = (2 : ℝ) * 2 := by
  intro p v hp hv
  have established := (exercise_GradientMountain_6 p v hp hv).left
  rw [established]

-- exercise_GreensGarden_1
example : (2 : ℝ) • (![1, 0, 0] : Vec) = (2 : ℝ) • (fun t : ℝ => (![1, t, 0] : Vec)) 0 := by
  have established := exercise_GreensGarden_1.left
  rw [established]

-- exercise_GreensGarden_2
example : ((2 : ℝ) * squareCirculation fun p => (![0, p 0, 0] : Vec)) = (2 : ℝ) * 1 := by
  have established := exercise_GreensGarden_2
  rw [established]

-- exercise_GreensGarden_3
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 = (2 : ℝ) * 1 := by
  have established := exercise_GreensGarden_3
  rw [established]

-- exercise_GreensGarden_4
example : ((2 : ℝ) * squareCirculation fun p => (![0, 3 * p 0, 0] : Vec)) =
  (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, 3 * p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 := by
  have established := exercise_GreensGarden_4
  rw [established]

-- exercise_GreensGarden_5
example : ((2 : ℝ) * squareOutwardFlux fun p => (![p 0, p 1, 0] : Vec)) =
  (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, divergence (fun p => (![p 0, p 1, 0] : Vec)) (![x, y, 0] : Vec) := by
  have established := exercise_GreensGarden_5
  rw [established]

-- exercise_GreensGarden_6
example : (2 : ℝ) * squareCirculation rotation = (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, (1 : ℝ) := by
  have established := exercise_GreensGarden_6.left
  rw [established]

-- exercise_MultivariableLandscapes_1
example : (2 : ℝ) * (1 ^ 2 + 0 ^ 2) ≤ (2 : ℝ) * 4 := by
  have established := exercise_MultivariableLandscapes_1.left
  linarith [established]

-- exercise_MultivariableLandscapes_2
example : (2 : ℝ) * squarePotential (![1, 2, 2] : Vec) = (2 : ℝ) * 9 := by
  have established := exercise_MultivariableLandscapes_2
  rw [established]

-- exercise_MultivariableLandscapes_3
example : ContinuousAt squarePotential (![2, 0, 1] : Vec) := by
  exact exercise_MultivariableLandscapes_3.continuousAt

-- exercise_MultivariableLandscapes_4
example (L : ℝ) (h : LimitAtOrigin squarePotential L) : L = 0 := by
  exact tendsto_nhds_unique h exercise_MultivariableLandscapes_4

-- exercise_MultivariableLandscapes_5
example : ¬ PuncturedLimit pathRatio 3 := by
  intro h
  apply exercise_MultivariableLandscapes_5
  use 3

-- exercise_MultivariableLandscapes_6
example : ContinuousAt (fun p : Vec => if p = 0 then 0 else squarePotential p) (![2, 0, 1] : Vec) := by
  exact exercise_MultivariableLandscapes_6.continuousAt

-- exercise_OptimizationArena_1
example : ∀ (x y : ℝ),
  x = 0 ∧ y = 0 ↔
    partialX (fun a b => a ^ 2 + b ^ 2) x y = 0 ∧ partialY (fun a b => a ^ 2 + b ^ 2) x y = 0 := by
  intro x y
  have established := exercise_OptimizationArena_1 x y
  exact established.symm

-- exercise_OptimizationArena_2
example : (2 : ℝ) * partialX (fun x y => partialX (fun a b => a ^ 2 + b ^ 2) x y) 0 0 = (2 : ℝ) * 2 := by
  have established := exercise_OptimizationArena_2.left.left
  rw [established]

-- exercise_OptimizationArena_3
example : ∀ (t : ℝ), t ≠ 0 → (2 : ℝ) * 0 < (2 : ℝ) * (t ^ 2 - 0 ^ 2) := by
  intro t ht
  have established := (exercise_OptimizationArena_3 t ht).left
  linarith [established]

-- exercise_OptimizationArena_4
example : ∀ (x y : ℝ), x ^ 2 + y ^ 2 ≤ 1 → (2 : ℝ) * 0 ≤ (2 : ℝ) * (x ^ 2 + y ^ 2) := by
  intro x y h
  have established := (exercise_OptimizationArena_4 x y h).left
  linarith [established]

-- exercise_OptimizationArena_5
example (x y l : ℝ) (hx : 1=l*(2*x)) (hy : 1=l*(2*y)) (hc : x^2+y^2=2) : x = y := by
  apply Or.elim (exercise_OptimizationArena_5 x y l hx hy hc)
  · intro h
    rw [h.1, h.2.1]
  · intro h
    rw [h.1, h.2.1]

-- exercise_OptimizationArena_6
example : (2 : ℝ) * ((1 : ℝ)^2 + 1^2) = 4 := by
  rw [exercise_OptimizationArena_6.1.1]
  norm_num

-- exercise_PartialDerivativeLab_1
example : ∀ (x y : ℝ), (2 : ℝ) * partialX (fun s t => s ^ 2 + t ^ 2) x y = (2 : ℝ) * ((2 : ℝ) * x) := by
  intro x y
  have established := exercise_PartialDerivativeLab_1 x y
  rw [established]

-- exercise_PartialDerivativeLab_2
example : ∀ (x y : ℝ), (2 : ℝ) * partialY (fun s t => s ^ 2 + t ^ 2) x y = (2 : ℝ) * (y + y) := by
  intro x y
  have established := exercise_PartialDerivativeLab_2 x y
  rw [established]

-- exercise_PartialDerivativeLab_3
example : ∀ (x y : ℝ), (2 : ℝ) * partialX (fun s t => partialX (fun a b => a ^ 2 + b ^ 2) s t) x y = (2 : ℝ) * 2 := by
  intro x y
  have established := (exercise_PartialDerivativeLab_3 x y).left
  rw [established]

-- exercise_PartialDerivativeLab_4
example : ∀ (x y : ℝ),
  (2 : ℝ) * partialY (fun s t => partialX (fun a b => a * b) s t) x y =
    (2 : ℝ) * partialX (fun s t => partialY (fun a b => a * b) s t) x y := by
  intro x y
  have established := exercise_PartialDerivativeLab_4 x y
  rw [established]

-- exercise_PartialDerivativeLab_5
example : ∀ (h k : ℝ), (2 : ℝ) * ((1 + h) ^ 2 + (1 + k) ^ 2 - (2 + (2 : ℝ) * h + (2 : ℝ) * k)) = (2 : ℝ) * (h ^ 2 + k ^ 2) := by
  intro h k
  have established := exercise_PartialDerivativeLab_5 h k
  rw [established]

-- exercise_PartialDerivativeLab_6
example (q : Vec) (h : q 0 = 1) : onPlane ![2,0,0] ![1,0,0] q := by
  apply (exercise_PartialDerivativeLab_6 q).2.2.2.mpr
  exact h

-- exercise_PathIntegralTrails_1
example : ∀ (A B : Vec), (2 : ℝ) • (fun t : ℝ => (1 - t) • A + t • B) 0 = (2 : ℝ) • A := by
  intro A B
  have established := (exercise_PathIntegralTrails_1 A B).left
  rw [established]

-- exercise_PathIntegralTrails_2
example : (2 : ℝ) * scalarLineIntegral (fun p => p 0) (fun t : ℝ => (![t, 0, 0] : Vec)) 0 2 = (2 : ℝ) * 2 := by
  have established := exercise_PathIntegralTrails_2
  rw [established]

-- exercise_PathIntegralTrails_3
example : (2 : ℝ) * work (fun p => (![p 0, 0, 0] : Vec)) (fun t : ℝ => (![t, 0, 0] : Vec)) 0 2 = (2 : ℝ) * 2 := by
  have established := exercise_PathIntegralTrails_3
  rw [established]

-- exercise_PathIntegralTrails_4
example : ∀ (F : VectorCalculus.Field) (c : ℝ → Vec) (a b : ℝ), (2 : ℝ) * work F c b a = (2 : ℝ) * -work F c a b := by
  intro F c a b
  have established := exercise_PathIntegralTrails_4 F c a b
  rw [established]

-- exercise_PathIntegralTrails_5
example : ∀ (F : VectorCalculus.Field) (f : ScalarField) (c : ℝ → Vec) (a b : ℝ),
  RegularPath c a b →
    PotentialAlong F f c a b → WorkIntegrable F c a b → (2 : ℝ) * work F c a b = (2 : ℝ) * (f (c b) - f (c a)) := by
  intro F f c a b hcurve hc hi
  have established := exercise_PathIntegralTrails_5 F f c a b hcurve hc hi
  rw [established]

-- exercise_PathIntegralTrails_6
example : ∀ (c d : ℝ → Vec),
  c 0 = d 0 →
    c 1 = d 1 →
      RegularPath c 0 1 →
        RegularPath d 0 1 →
          IntervalIntegrable (fun t : ℝ => deriv (fun s => c s 0) t) volume 0 1 →
            IntervalIntegrable (fun t : ℝ => deriv (fun s => d s 0) t) volume 0 1 →
              (2 : ℝ) * work (fun x => (![1, 0, 0] : Vec)) c 0 1 = (2 : ℝ) * (c 1 0 - c 0 0) := by
  intro c d h0 h1 hc hd hic hid
  have established := (exercise_PathIntegralTrails_6 c d h0 h1 hc hd hic hid).left
  rw [established]

-- exercise_SpaceExplorer_1
example : ∃ q : Vec, onLine ![1,0,2] ![1,2,-1] q := by
  use ![3,4,0]
  exact exercise_SpaceExplorer_1

-- exercise_SpaceExplorer_2
example : ∀ (q : Vec), q 2 = 3 ↔ onPlane (![0, 0, 2] : Vec) (![0, 0, 3] : Vec) q := by
  intro q
  have established := exercise_SpaceExplorer_2 q
  exact established.symm

-- exercise_SpaceExplorer_3
example : ∃ q : Vec, onLine ![0,0,0] ![0,0,1] q ∧ onPlane ![0,0,1] ![0,0,3] q := by
  use ![0,0,3]
  exact exercise_SpaceExplorer_3

-- exercise_SpaceExplorer_4
example : (2 : ℝ) * planeDistance (![0, 0, 1] : Vec) (![0, 0, 1] : Vec) (![2, -3, 4] : Vec) = (2 : ℝ) * 3 := by
  have established := exercise_SpaceExplorer_4
  rw [established]

-- exercise_SpaceExplorer_5
example : ∀ (x y z : ℝ), z = x ^ 2 ↔ z = x ^ 2 + 0 ^ 2 := by
  intro x y z
  have established := (exercise_SpaceExplorer_5 x y z).left
  exact established.symm

-- exercise_SpaceExplorer_6
example : (2 : ℝ) • cross ((![1, 0, 0] : Vec) - (![0, 0, 0] : Vec)) ((![0, 1, 0] : Vec) - (![0, 0, 0] : Vec)) = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  have established := exercise_SpaceExplorer_6.left
  rw [established]

-- exercise_StokesSummit_1
example : ∀ (t : ℝ), (2 : ℝ) • patch t 0 = (2 : ℝ) • (![t, 0, 0] : Vec) := by
  intro t
  have established := (exercise_StokesSummit_1 t).left
  rw [established]

-- exercise_StokesSummit_2
example : ∀ (t : ℝ), (2 : ℝ) • surfaceNormal patch 0 0 = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  intro t
  have established := (exercise_StokesSummit_2 t).left
  rw [established]

-- exercise_StokesSummit_3
example : ∀ (u v : ℝ), (2 : ℝ) * dot (curl (fun p => (![0, p 0, 0] : Vec)) (patch u v)) (surfaceNormal patch u v) = (2 : ℝ) * 1 := by
  intro u v
  have established := exercise_StokesSummit_3 u v
  rw [established]

-- exercise_StokesSummit_4
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) = (2 : ℝ) * 2 := by
  have established := exercise_StokesSummit_4
  rw [established]

-- exercise_StokesSummit_5
example : ((2 : ℝ) * squareCirculation fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) =
  (2 : ℝ) * surfaceFlux (curl fun p => (![0, (2 : ℝ) * p 0, 0] : Vec)) patch 0 1 0 1 := by
  have established := exercise_StokesSummit_5
  rw [established]

-- exercise_StokesSummit_6
example : (2 : ℝ) * surfaceFlux (curl (fun p => ![0,p 0,0])) liftedPatch 0 1 0 1 =
    (2 : ℝ) * surfaceFlux (curl (fun p => ![0,p 0,0])) patch 0 1 0 1 := by
  rw [exercise_StokesSummit_6.2]

-- exercise_SurfaceExpedition_1
example : ∀ (u v : ℝ), (2 : ℝ) * patch u v 2 = (2 : ℝ) * 0 := by
  intro u v
  have established := (exercise_SurfaceExpedition_1 u v).left
  rw [established]

-- exercise_SurfaceExpedition_2
example : ∀ (u v : ℝ), (2 : ℝ) • velocity (fun t : ℝ => patch t v) u = (2 : ℝ) • (![1, 0, 0] : Vec) := by
  intro u v
  have established := (exercise_SurfaceExpedition_2 u v).left
  rw [established]

-- exercise_SurfaceExpedition_3
example : ∀ (u v : ℝ), (2 : ℝ) * length (surfaceNormal patch u v) = (2 : ℝ) * 1 := by
  intro u v
  have established := exercise_SurfaceExpedition_3 u v
  rw [established]

-- exercise_SurfaceExpedition_4
example : (2 : ℝ) * surfaceIntegral (fun p => p 0) patch 0 1 0 1 = (2 : ℝ) * (1 / 2) := by
  have established := exercise_SurfaceExpedition_4
  rw [established]

-- exercise_SurfaceExpedition_5
example : (2 : ℝ) * surfaceFlux (fun x => (![0, 0, 1] : Vec)) patch 0 1 0 1 = (2 : ℝ) * 1 := by
  have established := exercise_SurfaceExpedition_5
  rw [established]

-- exercise_SurfaceExpedition_6
example : (2 : ℝ) * surfaceFlux (fun x => (![0, 0, 1] : Vec)) (fun u v => (![v, u, 0] : Vec)) 0 1 0 1 =
  (2 : ℝ) * -surfaceFlux (fun x => (![0, 0, 1] : Vec)) patch 0 1 0 1 := by
  have established := exercise_SurfaceExpedition_6.left
  rw [established]

-- exercise_TripleIntegralCaverns_1
example : (2 : ℝ) * ∫ (x : ℝ) in 0..2, ∫ (y : ℝ) in 0..3, ∫ (z : ℝ) in 0..4, (1 : ℝ) = (2 : ℝ) * 24 := by
  have established := exercise_TripleIntegralCaverns_1
  rw [established]

-- exercise_TripleIntegralCaverns_2
example : ∀ (x y z : ℝ), 0 ≤ z ∧ z ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ↔ 0 ≤ x ∧ x ≤ 1 ∧ 0 ≤ y ∧ y ≤ 1 ∧ 0 ≤ z ∧ z ≤ x := by
  intro x y z
  have established := exercise_TripleIntegralCaverns_2 x y z
  exact established.symm

-- exercise_TripleIntegralCaverns_3
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, ∫ (z : ℝ) in 0..x, (1 : ℝ) = (2 : ℝ) * (1 / 2) := by
  have established := exercise_TripleIntegralCaverns_3
  rw [established]

-- exercise_TripleIntegralCaverns_4
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, x ^ 2 = (2 : ℝ) * (1 / 3) := by
  have established := exercise_TripleIntegralCaverns_4
  rw [established]

-- exercise_TripleIntegralCaverns_5
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, x * x ^ 2 = (2 : ℝ) * (1 / 4) := by
  have established := exercise_TripleIntegralCaverns_5
  rw [established]

-- exercise_TripleIntegralCaverns_6
example : (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1, (1 : ℝ) = (2 : ℝ) * 1 := by
  have established := exercise_TripleIntegralCaverns_6.left
  rw [established]

-- exercise_VectorFieldObservatory_1
example : (2 : ℝ) • radial (![2, 0, 0] : Vec) = (2 : ℝ) • (![2, 0, 0] : Vec) := by
  have established := exercise_VectorFieldObservatory_1.left
  rw [established]

-- exercise_VectorFieldObservatory_2
example : ∀ (p : Vec), (2 : ℝ) • gradient (fun q => q 0 * q 1) p = (2 : ℝ) • (![p 1, p 0, 0] : Vec) := by
  intro p
  have established := exercise_VectorFieldObservatory_2 p
  rw [established]

-- exercise_VectorFieldObservatory_3
example : ∀ (p : Vec), (2 : ℝ) * divergence radial p = (2 : ℝ) * 3 := by
  intro p
  have established := exercise_VectorFieldObservatory_3 p
  rw [established]

-- exercise_VectorFieldObservatory_4
example : ∀ (p : Vec), (2 : ℝ) • curl rotation p = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  intro p
  have established := exercise_VectorFieldObservatory_4 p
  rw [established]

-- exercise_VectorFieldObservatory_5
example : ∀ (p : Vec), (2 : ℝ) • curl (gradient fun q => q 0) p = (2 : ℝ) • 0 := by
  intro p
  have established := (exercise_VectorFieldObservatory_5 p).left
  rw [established]

-- exercise_VectorFieldObservatory_6
example : ∃ f : ScalarField, ∀ p, gradient f p = (![p 1,p 0,0] : Vec) := by
  apply Exists.elim exercise_VectorFieldObservatory_6
  intro f hf
  use f
  exact hf.2

-- exercise_Vectors_1
example : (2 : ℝ) * (![2, -1, 3] : Vec) 1 = (2 : ℝ) * -1 := by
  have established := exercise_Vectors_1
  rw [established]

-- exercise_Vectors_2
example : (2 : ℝ) • ((![1, 2, 0] : Vec) + (2 : ℝ) • (![0, -1, 3] : Vec)) = (2 : ℝ) • (![1, 0, 6] : Vec) := by
  have established := exercise_Vectors_2
  rw [established]

-- exercise_Vectors_3
example : (2 : ℝ) * dot (![1, 2, -1] : Vec) (![3, 0, 4] : Vec) = (2 : ℝ) * -1 := by
  have established := exercise_Vectors_3
  rw [established]

-- exercise_Vectors_4
example : (2 : ℝ) * dot (![1, 1, 0] : Vec) (![1, -1, 0] : Vec) = (2 : ℝ) * 0 := by
  have established := exercise_Vectors_4.left
  rw [established]

-- exercise_Vectors_5
example : (2 : ℝ) • cross (![1, 0, 0] : Vec) (![0, 1, 0] : Vec) = (2 : ℝ) • (![0, 0, 1] : Vec) := by
  have established := exercise_Vectors_5.left
  rw [established]

-- exercise_Vectors_6
example : (2 : ℝ) • projection (![3, 1, 2] : Vec) (![1, 1, 0] : Vec) = (2 : ℝ) • (![2, 2, 0] : Vec) := by
  have established := exercise_Vectors_6.left
  rw [established]

-- hasDerivAt_pow
example (t : ℝ) : HasDerivAt (fun s : ℝ => s^3) (3*t^2) t := by
  have h := hasDerivAt_pow 3 t
  norm_num at h
  exact h

-- have
example (x y z : ℝ) (hxy : x = y) (hyz : y = z) : x = z := by
  have firstStep : x = y := hxy
  rw [firstStep]
  exact hyz

-- integral_id
example : ∀ {a b : ℝ}, (2 : ℝ) * ∫ (x : ℝ) in a..b, x = (2 : ℝ) * ((b ^ 2 - a ^ 2) / 2) := by
  intro a b
  have established := integral_id (a := a) (b := b)
  rw [established]

-- integral_pow
example : ∀ {a b : ℝ} (n : ℕ), (2 : ℝ) * ∫ (x : ℝ) in a..b, x ^ n = (2 : ℝ) * ((b ^ (n + 1) - a ^ (n + 1)) / (↑n + 1)) := by
  intro a b n
  have established := integral_pow (a := a) (b := b) n
  rw [established]

-- integral_sin
example : ∀ {a b : ℝ}, (2 : ℝ) * ∫ (x : ℝ) in a..b, Real.sin x = (2 : ℝ) * (Real.cos a - Real.cos b) := by
  intro a b
  have established := integral_sin (a := a) (b := b)
  rw [established]

-- intervalIntegral.integral_const_mul
example (f : ℝ → ℝ) : (∫ t : ℝ in 0..4, 3*f t) = 3*(∫ t : ℝ in 0..4, f t) := by
  rw [intervalIntegral.integral_const_mul]

-- intervalIntegral.integral_div
example (f : ℝ → ℝ) : (∫ t : ℝ in 0..4, f t/3) = (∫ t : ℝ in 0..4, f t)/3 := by
  rw [intervalIntegral.integral_div]

-- intervalIntegral.integral_mul_const
example (f : ℝ → ℝ) : (∫ t : ℝ in 0..4, f t*3) = (∫ t : ℝ in 0..4, f t)*3 := by
  rw [intervalIntegral.integral_mul_const]

-- intervalIntegral.integral_sub
example (f g : ℝ → ℝ) (hf : IntervalIntegrable f volume 0 4) (hg : IntervalIntegrable g volume 0 4) :
    (∫ t : ℝ in 0..4, f t-g t) = (∫ t : ℝ in 0..4, f t) - (∫ t : ℝ in 0..4, g t) := by
  rw [intervalIntegral.integral_sub hf hg]

-- intro
example : ∀ x : ℝ, x = x := by
  intro x
  rfl

-- le_of_sq_le_sq
example (x : ℝ) (h : x^2 ≤ (7 : ℝ)^2) : x ≤ 7 := by
  apply le_of_sq_le_sq h
  norm_num

-- le_trans
example (x : ℝ) (h : x ≤ 3) : x ≤ 8 := by
  apply le_trans h
  norm_num

-- left
example (p : Vec) (h : p 0 = 2) : p 0 = 2 ∨ p 0 = 5 := by
  left
  exact h

-- linarith
example (x y : ℝ) (hsum : x + y = 5) (hy : y = 2) : x = 3 := by
  linarith

-- Matrix.det_fin_two
example : Matrix.det ((!![(3 : ℝ), 1; 0, 2] : Matrix (Fin 2) (Fin 2) ℝ)) = 6 := by
  rw [Matrix.det_fin_two]
  norm_num

-- Matrix.one_apply
example : (1 : Matrix (Fin 3) (Fin 3) ℝ) 0 2 = 0 := by
  rw [Matrix.one_apply]
  norm_num

-- mul_left_cancel₀
example (x y : ℝ) (h : 3*x = 3*y) : x = y := by
  apply mul_left_cancel₀ (by norm_num : (3 : ℝ) ≠ 0)
  exact h

-- mul_nonneg
example (x : ℝ) (hx : 0 ≤ x) : 0 ≤ x * 5 := by
  apply mul_nonneg hx
  norm_num

-- norm_num
example : (2 : ℝ) + 3 * 4 = 14 := by
  norm_num

-- not_exists
example (P : ℝ → Prop) : (∀ t, ¬ P t) ↔ ¬ ∃ t, P t := by
  exact (not_exists (p := P)).symm

-- one_mul
example (x : ℝ) : 1 * (x + 4) = x + 4 := by
  exact one_mul (x + 4)

-- Or.elim
example (x : ℝ) (h : x = 2 ∨ x = 5) : 2 ≤ x := by
  apply Or.elim h
  · intro hx
    rw [hx]
  · intro hx
    rw [hx]
    norm_num

-- Real.sin_nonneg_of_mem_Icc
example : ∀ {x : ℝ}, x ∈ Set.Icc 0 Real.pi → (2 : ℝ) * 0 ≤ (2 : ℝ) * Real.sin x := by
  intro x hx
  have established := Real.sin_nonneg_of_mem_Icc hx
  linarith [established]

-- Real.sin_sq_add_cos_sq
example : ∀ (x : ℝ), (2 : ℝ) * (Real.sin x ^ 2 + Real.cos x ^ 2) = (2 : ℝ) * 1 := by
  intro x
  have established := Real.sin_sq_add_cos_sq x
  rw [established]

-- rfl
example : (![8, 4, -2] : Vec) 2 = -2 := by
  rfl

-- right
example (p : Vec) (h : p 0 = 5) : p 0 = 2 ∨ p 0 = 5 := by
  right
  exact h

-- ring
example (x : ℝ) : (x + 3)^2 - (x^2 + 6*x) = 9 := by
  ring

-- rw
example (u v w : Vec) (h : u = v) : dot u w = dot v w := by
  rw [h]

-- simp
example (x : ℝ) : x + 0 = x := by
  simp

-- sq_nonneg
example (x : ℝ) : 0 ≤ (x - 3)^2 := by
  exact sq_nonneg (x - 3)

-- sq_pos_of_ne_zero
example (x : ℝ) (h : x ≠ 2) : 0 < (x - 2)^2 := by
  apply sq_pos_of_ne_zero
  intro hz
  apply h
  linarith

-- use
example : ∃ t : ℝ, (![t, 3, 0] : Vec) 0 = 5 := by
  use 5
  rfl

-- VectorCalculus.ascent_squares
example : ∀ (u : Vec),
  (2 : ℝ) * ((3 * u 0 + 4 * u 1) ^ 2 + (4 * u 0 - 3 * u 1) ^ 2 + 25 * u 2 ^ 2) = (2 : ℝ) * (25 * lengthSq u) := by
  intro u
  have established := ascent_squares u
  rw [established]

-- VectorCalculus.constant_integral
example : ∀ (a b k : ℝ), (2 : ℝ) * ∫ (x : ℝ) in a..b, k = (2 : ℝ) * ((b - a) * k) := by
  intro a b k
  have established := constant_integral a b k
  rw [established]

-- VectorCalculus.continuous_fill_origin
example (f : ScalarField) (hc : Continuous f) (h0 : f 0 = 0) :
    ContinuousAt (fun p : Vec => if p = 0 then 0 else f p) (![3, 1, 0] : Vec) := by
  exact (continuous_fill_origin hc h0).continuousAt

-- VectorCalculus.continuous_sum_squares
example (f g h : ScalarField) (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    ContinuousAt (fun p => f p^2 + g p^2 + h p^2) (![2, 3, 0] : Vec) := by
  exact (continuous_sum_squares hf hg hh).continuousAt

-- VectorCalculus.curl_congr
example : ∀ {F G : VectorCalculus.Field}, (∀ (p : Vec), F p = G p) → ∀ (p : Vec), (2 : ℝ) • curl F p = (2 : ℝ) • curl G p := by
  intro F G h p
  have established := curl_congr h p
  rw [established]

-- VectorCalculus.derivative_chain
example (t : ℝ) : HasDerivAt (fun s : ℝ => (s^2)^3) ((3*(t^2)^2)*(2*t)) t := by
  apply derivative_chain (f := fun s : ℝ => s^3) (g := fun s : ℝ => s^2) (a := 3*(t^2)^2) (b := 2*t)
  · have h := hasDerivAt_pow 3 (t^2)
    norm_num at h
    exact h
  · have h := hasDerivAt_pow 2 t
    norm_num at h
    exact h

-- VectorCalculus.derivative_value
example (f : ℝ → ℝ) (a t : ℝ) (h : HasDerivAt f a t) : HasDerivAt f (a+0) t := by
  apply derivative_value h
  ring

-- VectorCalculus.directional_coordinate
example : ∀ (j : Fin 3) (p u : Vec), (2 : ℝ) * directional (fun q => q j) p u = (2 : ℝ) * u j := by
  intro j p u
  have established := directional_coordinate j p u
  rw [established]

-- VectorCalculus.divergence_congr
example : ∀ {F G : VectorCalculus.Field},
  (∀ (p : Vec), F p = G p) → ∀ (p : Vec), (2 : ℝ) * divergence F p = (2 : ℝ) * divergence G p := by
  intro F G h p
  have established := divergence_congr h p
  rw [established]

-- VectorCalculus.divergence_diagonal
example : ∀ (a b c : ℝ) (p : Vec), (2 : ℝ) * divergence (fun q => (![a * q 0, b * q 1, c * q 2] : Vec)) p = (2 : ℝ) * (a + b + c) := by
  intro a b c p
  have established := divergence_diagonal a b c p
  rw [established]

-- VectorCalculus.dot_cross_left
example : ∀ (u v : Vec), (2 : ℝ) * dot u (cross u v) = (2 : ℝ) * 0 := by
  intro u v
  have established := dot_cross_left u v
  rw [established]

-- VectorCalculus.gauss_diagonal
example : ∀ (a b c : ℝ),
  ((2 : ℝ) * cubeFlux fun p => (![a * p 0, b * p 1, c * p 2] : Vec)) =
    2 *
      ∫ (x : ℝ) (y : ℝ) (z : ℝ) in 0..1,
        divergence (fun p => (![a * p 0, b * p 1, c * p 2] : Vec)) (![x, y, z] : Vec) := by
  intro a b c
  have established := gauss_diagonal a b c
  rw [established]

-- VectorCalculus.gradient_components
example : ∀ (f : ScalarField) (p : Vec),
  (2 : ℝ) • gradient f p = (2 : ℝ) • (![coordPartial f p 0, coordPartial f p 1, coordPartial f p 2] : Vec) := by
  intro f p
  have established := gradient_components f p
  rw [established]

-- VectorCalculus.green_shear
example : ∀ (k : ℝ),
  ((2 : ℝ) * squareCirculation fun p => (![0, k * p 0, 0] : Vec)) =
    (2 : ℝ) * ∫ (x : ℝ) (y : ℝ) in 0..1, curl (fun p => (![0, k * p 0, 0] : Vec)) (![x, y, 0] : Vec) 2 := by
  intro k
  have established := green_shear k
  rw [established]

-- VectorCalculus.integral_values
example : ∀ {f g : ℝ → ℝ} {a b : ℝ},
  (∀ (t : ℝ), f t = g t) → (2 : ℝ) * ∫ (t : ℝ) in a..b, f t = (2 : ℝ) * ∫ (t : ℝ) in a..b, g t := by
  intro f g a b h
  have established := integral_values (a := a) (b := b) h
  rw [established]

-- VectorCalculus.limit_diagonal
example (f : ScalarField) (h : PuncturedLimit f 7) : PathLimit (fun t : ℝ => f ![t,t,0]) 7 := by
  exact limit_diagonal h

-- VectorCalculus.limit_horizontal
example (f : ScalarField) (h : PuncturedLimit f 5) : PathLimit (fun t : ℝ => f ![t,0,0]) 5 := by
  exact limit_horizontal h

-- VectorCalculus.limit_of_continuous
example (f : ScalarField) (hc : Continuous f) (hv : f 0 = 4) : LimitAtOrigin f 4 := by
  exact limit_of_continuous hc hv

-- VectorCalculus.matrix_eq
example : ∀ {A B : Matrix (Fin 3) (Fin 3) ℝ},
  A 0 0 = B 0 0 →
    A 0 1 = B 0 1 →
      A 0 2 = B 0 2 →
        A 1 0 = B 1 0 →
          A 1 1 = B 1 1 → A 1 2 = B 1 2 → A 2 0 = B 2 0 → A 2 1 = B 2 1 → A 2 2 = B 2 2 → B = A := by
  intro A B h00 h01 h02 h10 h11 h12 h20 h21 h22
  have established := matrix_eq h00 h01 h02 h10 h11 h12 h20 h21 h22
  rw [established]

-- VectorCalculus.normal_components
example : ∀ (x y z : ℝ → ℝ → ℝ) (u v : ℝ),
  (2 : ℝ) • surfaceNormal (fun s t => (![x s t, y s t, z s t] : Vec)) u v =
    (2 : ℝ) •
      cross (![partialX x u v, partialX y u v, partialX z u v] : Vec)
        (![partialY x u v, partialY y u v, partialY z u v] : Vec) := by
  intro x y z u v
  have established := normal_components x y z u v
  rw [established]

-- VectorCalculus.normal_congr
example : ∀ {s t : ℝ → ℝ → Vec},
  (∀ (u v : ℝ), s u v = t u v) → ∀ (u v : ℝ), (2 : ℝ) • surfaceNormal s u v = (2 : ℝ) • surfaceNormal t u v := by
  intro s t h u v
  have established := normal_congr h u v
  rw [established]

-- VectorCalculus.normal_graph
example : ∀ (f : ℝ → ℝ → ℝ) (u v : ℝ),
  (2 : ℝ) • surfaceNormal (fun s t => (![s, t, f s t] : Vec)) u v = (2 : ℝ) • (![-partialX f u v, -partialY f u v, 1] : Vec) := by
  intro f u v
  have established := normal_graph f u v
  rw [established]

-- VectorCalculus.partial_constant
example : ∀ (a : ℝ) (p : Vec) (i : Fin 3), (2 : ℝ) * coordPartial (fun x => a) p i = (2 : ℝ) * 0 := by
  intro a p i
  have established := partial_constant a p i
  rw [established]

-- VectorCalculus.partial_coordinate
example : ∀ (j : Fin 3) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => q j) p i = (2 : ℝ) * if i = j then 1 else 0 := by
  intro j p i
  have established := partial_coordinate j p i
  rw [established]

-- VectorCalculus.partial_div_const
example : ∀ (f : ScalarField) (a : ℝ) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => f q / a) p i = (2 : ℝ) * (coordPartial f p i / a) := by
  intro f a p i
  have established := partial_div_const f a p i
  rw [established]

-- VectorCalculus.partial_neg
example : ∀ (f : ScalarField) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => -f q) p i = (2 : ℝ) * -coordPartial f p i := by
  intro f p i
  have established := partial_neg f p i
  rw [established]

-- VectorCalculus.partial_scaled_coordinate
example : ∀ (a : ℝ) (j : Fin 3) (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => a * q j) p i = (2 : ℝ) * if i = j then a else 0 := by
  intro a j p i
  have established := partial_scaled_coordinate a j p i
  rw [established]

-- VectorCalculus.partial_sum_squares
example : ∀ (p : Vec) (i : Fin 3), (2 : ℝ) * coordPartial squarePotential p i = (2 : ℝ) * ((2 : ℝ) * p i) := by
  intro p i
  have established := partial_sum_squares p i
  rw [established]

-- VectorCalculus.partial_xy
example : ∀ (p : Vec) (i : Fin 3),
  (2 : ℝ) * coordPartial (fun q => q 0 * q 1) p i = (2 : ℝ) * if i = 0 then p 1 else if i = 1 then p 0 else 0 := by
  intro p i
  have established := partial_xy p i
  rw [established]

-- VectorCalculus.path_limit_of_values
example (g : ℝ → ℝ) (h : ∀ t, t ≠ 0 → g t = 3) : PathLimit g 3 := by
  exact path_limit_of_values h

-- VectorCalculus.path_limit_unique
example : ∀ {g : ℝ → ℝ} {a b : ℝ}, PathLimit g a → PathLimit g b → (2 : ℝ) * a = (2 : ℝ) * b := by
  intro g a b ha hb
  have established := path_limit_unique ha hb
  rw [established]

-- VectorCalculus.ratio_diagonal
example : ∀ (t : ℝ), t ≠ 0 → (2 : ℝ) * pathRatio (![t, t, 0] : Vec) = (2 : ℝ) * (1 / 2) := by
  intro t ht
  have established := ratio_diagonal t ht
  rw [established]

-- VectorCalculus.ratio_horizontal
example : ∀ (t : ℝ), (2 : ℝ) * pathRatio (![t, 0, 0] : Vec) = (2 : ℝ) * 0 := by
  intro t
  have established := ratio_horizontal t
  rw [established]

-- VectorCalculus.reverse_integral
example : ∀ (g : ℝ → ℝ) (a b : ℝ), (2 : ℝ) * ∫ (t : ℝ) in b..a, g t = (2 : ℝ) * -∫ (t : ℝ) in a..b, g t := by
  intro g a b
  have established := reverse_integral g a b
  rw [established]

-- VectorCalculus.stokes_shear_patch
example : ∀ (k : ℝ),
  ((2 : ℝ) * squareCirculation fun p => (![0, k * p 0, 0] : Vec)) =
    (2 : ℝ) * surfaceFlux (curl fun p => (![0, k * p 0, 0] : Vec)) patch 0 1 0 1 := by
  intro k
  have established := stokes_shear_patch k
  rw [established]

-- VectorCalculus.vector_components
example : ∀ (p : Vec), (2 : ℝ) • (![p 0, p 1, p 2] : Vec) = (2 : ℝ) • p := by
  intro p
  have established := vector_components p
  rw [established]

-- VectorCalculus.vector_eq
example : (![2, 4, 0] : Vec) + ![1, 0, 3] = ![3, 4, 3] := by
  apply vector_eq
  · norm_num
  · norm_num
  · norm_num

-- VectorCalculus.vector_ne_zero
example : (![0,7,0] : Vec) ≠ 0 := by
  apply vector_ne_zero 1
  norm_num

-- VectorCalculus.velocity_components
example : ∀ (x y z : ℝ → ℝ) (t : ℝ),
  (2 : ℝ) • velocity (fun s => (![x s, y s, z s] : Vec)) t = (2 : ℝ) • (![deriv x t, deriv y t, deriv z t] : Vec) := by
  intro x y z t
  have established := velocity_components x y z t
  rw [established]

-- VectorCalculus.velocity_congr
example : ∀ {c d : ℝ → Vec}, (∀ (t : ℝ), c t = d t) → ∀ (t : ℝ), (2 : ℝ) • velocity c t = (2 : ℝ) • velocity d t := by
  intro c d h t
  have established := velocity_congr h t
  rw [established]

-- VectorCalculus.work_eq_endpoint
example : ∀ (F : VectorCalculus.Field) (f : ScalarField) (c : ℝ → Vec) (a b : ℝ),
  (∀ t ∈ Set.uIcc a b, HasDerivAt (fun s => f (c s)) (dot (F (c t)) (velocity c t)) t) →
    IntervalIntegrable (fun t : ℝ => dot (F (c t)) (velocity c t)) volume a b →
      (2 : ℝ) * work F c a b = (2 : ℝ) * (f (c b) - f (c a)) := by
  intro F f c a b hchain hint
  have established := work_eq_endpoint F f c a b hchain hint
  rw [established]

-- VectorCalculus.work_first_coordinate
example : ∀ (c : ℝ → Vec) (a b : ℝ),
  RegularPath c a b →
    IntervalIntegrable (fun t : ℝ => deriv (fun s => c s 0) t) volume a b →
      (2 : ℝ) * work (fun x => (![1, 0, 0] : Vec)) c a b = (2 : ℝ) * (c b 0 - c a 0) := by
  intro c a b hc hi
  have established := work_first_coordinate c a b hc hi
  rw [established]
