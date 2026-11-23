import Game.Advanced
import Game.Coordinates
import Game.PathLimits

/-! Reusable mathematical rules for players coming from the Natural Number Game.
The implementation details live here; exercises still choose and apply the rules.
All limits, derivatives, and integrals retain the definitions in the shared modules. -/
noncomputable section
namespace VectorCalculus
open MeasureTheory intervalIntegral Filter
open scoped Topology

/-- Three component equalities suffice to prove equality of spatial vectors. -/
theorem vector_eq {u v : Vec} (hx : u 0 = v 0) (hy : u 1 = v 1)
    (hz : u 2 = v 2) : u = v := by
  funext i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

/-- Reassembling a vector from its three components recovers that vector. -/
theorem vector_components (p : Vec) : (![p 0,p 1,p 2] : Vec) = p := by
  apply vector_eq <;> rfl

/-- A vector with a nonzero component is nonzero. -/
theorem vector_ne_zero {v : Vec} (i : Fin 3) (h : v i ≠ 0) : v ≠ 0 := by
  intro hv
  exact h (congrFun hv i)

/-- Component derivatives compute the derivative of a parametrized spatial curve. -/
theorem velocity_components (x y z : ℝ → ℝ) (t : ℝ) :
    velocity (fun s => ![x s,y s,z s]) t = ![deriv x t,deriv y t,deriv z t] := by
  apply vector_eq <;> rfl

/-- Replacing an equal curve also replaces its component derivatives. -/
theorem velocity_congr {c d : ℝ → Vec} (h : ∀ t, c t = d t) (t : ℝ) :
    velocity c t = velocity d t := by
  have he : c = d := funext h
  rw [he]

/-- Display a gradient as its three partial derivatives. -/
theorem gradient_components (f : ScalarField) (p : Vec) :
    gradient f p = ![coordPartial f p 0,coordPartial f p 1,coordPartial f p 2] := by
  apply vector_eq <;> rfl

/-- Differentiating a coordinate gives one in its own direction and zero otherwise. -/
theorem partial_coordinate (j : Fin 3) (p : Vec) (i : Fin 3) :
    coordPartial (fun q => q j) p i = if i = j then 1 else 0 := by
  fin_cases i <;> fin_cases j <;> simp [coordPartial, Function.update]

/-- A constant scalar field has zero partial derivatives. -/
theorem partial_constant (a : ℝ) (p : Vec) (i : Fin 3) :
    coordPartial (fun _ => a) p i = 0 := by simp [coordPartial]

/-- The partial derivatives of a scaled coordinate. -/
theorem partial_scaled_coordinate (a : ℝ) (j : Fin 3) (p : Vec) (i : Fin 3) :
    coordPartial (fun q => a * q j) p i = if i = j then a else 0 := by
  fin_cases i <;> fin_cases j <;>
    simp [coordPartial, Function.update, deriv_const_mul_id]

/-- Negating a field negates its partial derivatives. -/
theorem partial_neg (f : ScalarField) (p : Vec) (i : Fin 3) :
    coordPartial (fun q => -f q) p i = -coordPartial f p i := by
  simp [coordPartial, deriv_neg]

/-- Division by a fixed scalar commutes with a partial derivative. -/
theorem partial_div_const (f : ScalarField) (a : ℝ) (p : Vec) (i : Fin 3) :
    coordPartial (fun q => f q / a) p i = coordPartial f p i / a := by
  simp [coordPartial, deriv_div_const]

/-- Equal vector fields have equal curls. -/
theorem curl_congr {F G : Field} (h : ∀ p, F p = G p) (p : Vec) :
    curl F p = curl G p := by rw [show F = G from funext h]

/-- Equal vector fields have equal divergences. -/
theorem divergence_congr {F G : Field} (h : ∀ p, F p = G p) (p : Vec) :
    divergence F p = divergence G p := by rw [show F = G from funext h]

/-- The product xy has coordinate partials y, x, and zero. -/
theorem partial_xy (p : Vec) (i : Fin 3) :
    coordPartial (fun q => q 0 * q 1) p i =
      if i = 0 then p 1 else if i = 1 then p 0 else 0 := by
  fin_cases i <;>
    simp [coordPartial, Function.update, deriv_mul_const_field, deriv_const_mul_field]

/-- The squared-distance field has partial derivative twice the chosen coordinate. -/
theorem partial_sum_squares (p : Vec) (i : Fin 3) :
    coordPartial squarePotential p i = 2 * p i := by
  fin_cases i <;> simp [coordPartial, squarePotential, Function.update,
    deriv_add_const, deriv_const_add, deriv_pow_field]

/-- A coordinate projection's total directional derivative is the chosen component.
This rate is per unit distance when the direction has Euclidean length one. -/
theorem directional_coordinate (j : Fin 3) (p u : Vec) :
    directional (fun q => q j) p u = u j := by
  let P : Vec →L[ℝ] ℝ := ContinuousLinearMap.proj j
  change fderiv ℝ P p u = u j
  rw [P.fderiv]
  rfl

/-- Chain rule stated as a derivative equality; both differentiability facts are required. -/
theorem derivative_chain {f g : ℝ → ℝ} {a b t : ℝ}
    (hf : HasDerivAt f a (g t)) (hg : HasDerivAt g b t) :
    HasDerivAt (fun s => f (g s)) (a * b) t := by
  exact hf.comp t hg

/-- Replace the displayed derivative value by an algebraically equal value. -/
theorem derivative_value {f : ℝ → ℝ} {a b t : ℝ}
    (h : HasDerivAt f a t) (hab : a = b) : HasDerivAt f b t := by rw [← hab]; exact h

/-- Entrywise equality for a 3 by 3 Jacobian; indices start at zero. -/
theorem matrix_eq {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (h00 : A 0 0 = B 0 0) (h01 : A 0 1 = B 0 1) (h02 : A 0 2 = B 0 2)
    (h10 : A 1 0 = B 1 0) (h11 : A 1 1 = B 1 1) (h12 : A 1 2 = B 1 2)
    (h20 : A 2 0 = B 2 0) (h21 : A 2 1 = B 2 1) (h22 : A 2 2 = B 2 2) : A = B := by
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- The identity behind the concrete (3,4,0) steepest-ascent bound. -/
theorem ascent_squares (u : Vec) :
    (3*u 0+4*u 1)^2+(4*u 0-3*u 1)^2+25*(u 2)^2 = 25*lengthSq u := by
  simp [lengthSq, dot]
  ring

/-- A constant integral is its value times the interval's signed length. -/
theorem constant_integral (a b k : ℝ) : (∫ _ : ℝ in a..b, k) = (b-a)*k := by
  simp [intervalIntegral.integral_const, smul_eq_mul]

/-- Pointwise equal integrands have equal interval integrals. -/
theorem integral_values {f g : ℝ → ℝ} {a b : ℝ} (h : ∀ t, f t = g t) :
    (∫ t in a..b, f t) = ∫ t in a..b, g t := by
  have he : f = g := funext h
  rw [he]

/-- The derivative columns give the oriented parameter normal. -/
theorem normal_congr {s t : ℝ → ℝ → Vec} (h : ∀ u v, s u v = t u v) (u v : ℝ) :
    surfaceNormal s u v = surfaceNormal t u v := by
  have he : s = t := funext (fun u => funext (h u))
  rw [he]

/-- The derivative columns give the oriented parameter normal. -/
theorem normal_components (x y z : ℝ → ℝ → ℝ) (u v : ℝ) :
    surfaceNormal (fun s t => ![x s t,y s t,z s t]) u v =
      cross ![partialX x u v,partialX y u v,partialX z u v]
        ![partialY x u v,partialY y u v,partialY z u v] := by
  simp [surfaceNormal, velocity_components, partialX, partialY]

/-- Graph normals have vertical component one, without assuming a unit normal. -/
theorem normal_graph (f : ℝ → ℝ → ℝ) (u v : ℝ) :
    surfaceNormal (fun s t => ![s,t,f s t]) u v =
      ![-partialX f u v,-partialY f u v,1] := by
  simp [normal_components, partialX, partialY, cross]

/-- A sum of squared continuous real functions is continuous. -/
theorem continuous_sum_squares {X : Type*} [TopologicalSpace X]
    {f g h : X → ℝ} (hf : Continuous f) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun p => f p ^ 2 + g p ^ 2 + h p ^ 2) := by fun_prop

/-- A readable name for the full multivariable limit at the origin. -/
abbrev LimitAtOrigin (f : ScalarField) (L : ℝ) : Prop :=
  Tendsto f (𝓝 (0 : Vec)) (𝓝 L)

/-- A readable name for the punctured multivariable limit at the origin. -/
abbrev PuncturedLimit (f : ScalarField) (L : ℝ) : Prop :=
  Tendsto f (𝓝[≠] (0 : Vec)) (𝓝 L)

/-- A scalar path limit excludes its zero parameter. -/
abbrev PathLimit (g : ℝ → ℝ) (L : ℝ) : Prop := Tendsto g (𝓝[≠] 0) (𝓝 L)

/-- Continuity and the value at zero give the full limit. -/
theorem limit_of_continuous {f : ScalarField} {L : ℝ}
    (hc : Continuous f) (hv : f 0 = L) : LimitAtOrigin f L := by
  rw [← hv]
  exact hc.continuousAt.tendsto

/-- A punctured multivariable limit restricts to the horizontal path. -/
theorem limit_horizontal {f : ScalarField} {L : ℝ} (h : PuncturedLimit f L) :
    PathLimit (fun t => f ![t,0,0]) L := by
  simpa [PathLimit, Function.comp_def] using h.comp (coordinatePath_tendsto 0)

/-- A punctured multivariable limit restricts to the diagonal path. -/
theorem limit_diagonal {f : ScalarField} {L : ℝ} (h : PuncturedLimit f L) :
    PathLimit (fun t => f ![t,t,0]) L := by
  simpa [PathLimit, Function.comp_def] using h.comp (coordinatePath_tendsto 1)

/-- A function constant for all nonzero parameters has that punctured limit. -/
theorem path_limit_of_values {g : ℝ → ℝ} {L : ℝ}
    (h : ∀ t, t ≠ 0 → g t = L) : PathLimit g L := by
  apply Tendsto.congr' (f₁ := fun _ => L) ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (h t ht).symm

/-- Real path limits are unique. -/
theorem path_limit_unique {g : ℝ → ℝ} {a b : ℝ}
    (ha : PathLimit g a) (hb : PathLimit g b) : a = b :=
  tendsto_nhds_unique ha hb

/-- Filling in the existing value at the origin preserves continuity. -/
theorem continuous_fill_origin {f : ScalarField} (hc : Continuous f) (h0 : f 0 = 0) :
    Continuous (fun p => if p = 0 then 0 else f p) := by
  have he : (fun p => if p = 0 then 0 else f p) = f := by
    funext p
    split_ifs with hp
    · simpa [hp] using h0.symm
    · rfl
  rw [he]
  exact hc

/-- Matching diagonal partials give the divergence of a diagonal linear field. -/
theorem divergence_diagonal (a b c : ℝ) (p : Vec) :
    divergence (fun q => ![a*q 0,b*q 1,c*q 2]) p = a+b+c := by
  simp [divergence, partial_scaled_coordinate]

/-- Curve regularity in the coordinate representation. -/
abbrev RegularPath (c : ℝ → Vec) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.uIcc a b, ∀ i : Fin 3, DifferentiableAt ℝ (fun s => c s i) t

/-- The potential differentiated along the path equals the work integrand. -/
abbrev PotentialAlong (F : Field) (f : ScalarField) (c : ℝ → Vec) (a b : ℝ) : Prop :=
  ∀ t ∈ Set.uIcc a b, HasDerivAt (fun s => f (c s)) (dot (F (c t)) (velocity c t)) t

/-- Integrability of the actual work integrand on the ordered or reversed interval. -/
abbrev WorkIntegrable (F : Field) (c : ℝ → Vec) (a b : ℝ) : Prop :=
  IntervalIntegrable (fun t => dot (F (c t)) (velocity c t)) volume a b

/-- Endpoint evaluation for the potential x, with explicit regularity and integrability. -/
theorem work_first_coordinate (c : ℝ → Vec) (a b : ℝ) (hc : RegularPath c a b)
    (hi : IntervalIntegrable (fun t => deriv (fun s => c s 0) t) volume a b) :
    work (fun _ => ![1,0,0]) c a b = c b 0-c a 0 := by
  simpa [work, dot, velocity] using
    intervalIntegral.integral_deriv_eq_sub (fun t ht => hc t ht 0) hi

end VectorCalculus
