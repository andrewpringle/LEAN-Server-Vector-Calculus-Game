import Game
import GameServer

open VectorCalculus
open MeasureTheory intervalIntegral
open scoped Topology
noncomputable section

/-! All 96 intended solutions must be playable with only the tools available at that level. -/

-- Vector Workshop: Coordinates
Runner "MyGame" "Vectors" 1 (difficulty := 2) (inventory := []) := by
  rfl

-- Vector Workshop: Adding and scaling
Runner "MyGame" "Vectors" 2 (difficulty := 2) (inventory := []) := by
  apply vector_eq
  · norm_num
  · norm_num
  · norm_num

-- Vector Workshop: The dot product
Runner "MyGame" "Vectors" 3 (difficulty := 2) (inventory := []) := by
  rw [dot]
  norm_num

-- Vector Workshop: Orthogonality and length
Runner "MyGame" "Vectors" 4 (difficulty := 2) (inventory := []) := by
  constructor
  · rw [dot]
    norm_num
  · rw [lengthSq, dot]
    norm_num

-- Vector Workshop: Crossing directions
Runner "MyGame" "Vectors" 5 (difficulty := 2) (inventory := []) := by
  constructor
  · apply vector_eq
    · norm_num [cross]
    · norm_num [cross]
    · norm_num [cross]
  · apply dot_cross_left

-- Vector Workshop: Boss: resolve a vector
Runner "MyGame" "Vectors" 6 (difficulty := 2) (inventory := []) := by
  have projected : projection ![3,1,2] ![1,1,0] = (![2,2,0] : Vec) := by
    apply vector_eq
    · norm_num [projection, lengthSq, dot]
    · norm_num [projection, lengthSq, dot]
    · norm_num [projection, lengthSq, dot]
  constructor
  · exact projected
  · rw [projected, dot]
    norm_num

-- Space Explorer: A point on a line
Runner "MyGame" "SpaceExplorer" 1 (difficulty := 2) (inventory := []) := by
  use 2
  apply vector_eq
  · norm_num
  · norm_num
  · norm_num

-- Space Explorer: A plane from a normal
Runner "MyGame" "SpaceExplorer" 2 (difficulty := 2) (inventory := []) := by
  constructor
  · intro h
    norm_num [onPlane, dot] at h
    linarith
  · intro h
    norm_num [onPlane, dot, h]

-- Space Explorer: Line meets plane
Runner "MyGame" "SpaceExplorer" 3 (difficulty := 2) (inventory := []) := by
  constructor
  · use 3
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · rw [onPlane, dot]
    norm_num

-- Space Explorer: Distance to a plane
Runner "MyGame" "SpaceExplorer" 4 (difficulty := 2) (inventory := []) := by
  rw [planeDistance, length, lengthSq, dot]
  norm_num [dot]

-- Space Explorer: A paraboloid and its traces
Runner "MyGame" "SpaceExplorer" 5 (difficulty := 2) (inventory := []) := by
  constructor
  · simp
  · exact eq_comm

-- Space Explorer: Boss: three points
Runner "MyGame" "SpaceExplorer" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · apply vector_eq
    · norm_num [cross]
    · norm_num [cross]
    · norm_num [cross]
  · constructor
    · apply vector_ne_zero 2
      norm_num
    · constructor
      · rw [onPlane, dot]
        norm_num
      · rw [onPlane, dot]
        norm_num

-- Curve Navigator: Endpoints of a curve
Runner "MyGame" "CurveNavigator" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num

-- Curve Navigator: Differentiate a curve
Runner "MyGame" "CurveNavigator" 2 (difficulty := 2) (inventory := []) := by
  rw [velocity_components]
  apply vector_eq
  · norm_num [deriv_pow_field]
  · norm_num [deriv_pow_field]
  · norm_num [deriv_pow_field]

-- Curve Navigator: Motion at an instant
Runner "MyGame" "CurveNavigator" 3 (difficulty := 2) (inventory := []) := by
  have vel (t : ℝ) : velocity (fun s => ![s,s^2,0]) t = (![1,2*t,0] : Vec) := by
    rw [velocity_components]
    apply vector_eq
    · norm_num [deriv_pow_field]
    · norm_num [deriv_pow_field]
    · norm_num [deriv_pow_field]
  constructor
  · norm_num [vel]
  · constructor
    · rw [velocity_congr vel, velocity_components]
      apply vector_eq
      · norm_num [deriv_const_mul_id]
      · norm_num [deriv_const_mul_id]
      · norm_num [deriv_const_mul_id]
    · rw [speed, vel 0]
      norm_num [length, lengthSq, dot]

-- Curve Navigator: Arc length of a segment
Runner "MyGame" "CurveNavigator" 4 (difficulty := 2) (inventory := []) := by
  have unitSpeed (t : ℝ) : speed (fun s => ![s,0,0]) t = 1 := by
    rw [speed, velocity_components]
    norm_num [length, lengthSq, dot]
  rw [arcLength, integral_values unitSpeed, constant_integral]
  norm_num

-- Curve Navigator: Turning on the circle
Runner "MyGame" "CurveNavigator" 5 (difficulty := 2) (inventory := []) := by
  have vel (s : ℝ) : velocity circle s = (![-Real.sin s,Real.cos s,0] : Vec) := by
    have coordinates (t : ℝ) : circle t = (![Real.cos t,Real.sin t,0] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  have acc : velocity (velocity circle) 0 = (![-1,0,0] : Vec) := by
    rw [velocity_congr vel, velocity_components]
    apply vector_eq
    · norm_num [deriv_neg]
    · norm_num [deriv_neg]
    · norm_num [deriv_neg]
  have sp : speed circle 0 = 1 := by
    rw [speed, vel 0]
    norm_num [length, lengthSq, dot]
  constructor
  · rw [unitTangent, sp, vel 0]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · rw [curvature, sp, vel 0, acc]
    norm_num [length, lengthSq, dot, cross]

-- Curve Navigator: Boss: the helix
Runner "MyGame" "CurveNavigator" 6 (difficulty := 2) (inventory := []) := by
  have vel (s : ℝ) : velocity helix s = (![-Real.sin s,Real.cos s,1] : Vec) := by
    have coordinates (t : ℝ) : helix t = (![Real.cos t,Real.sin t,t] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  constructor
  · apply vector_eq
    · norm_num [helix]
    · norm_num [helix]
    · norm_num [helix]
  · constructor
    · exact vel t
    · rw [vel t]
      norm_num [lengthSq, dot]
      linarith [Real.sin_sq_add_cos_sq t]

-- Multivariable Landscapes: A constrained domain
Runner "MyGame" "MultivariableLandscapes" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · norm_num
  · norm_num

-- Multivariable Landscapes: A level set
Runner "MyGame" "MultivariableLandscapes" 2 (difficulty := 2) (inventory := []) := by
  rw [squarePotential]
  norm_num

-- Multivariable Landscapes: Polynomial continuity
Runner "MyGame" "MultivariableLandscapes" 3 (difficulty := 2) (inventory := []) := by
  apply continuous_sum_squares
  · exact continuous_apply 0
  · exact continuous_apply 1
  · exact continuous_apply 2

-- Multivariable Landscapes: A limit from continuity
Runner "MyGame" "MultivariableLandscapes" 4 (difficulty := 2) (inventory := []) := by
  apply limit_of_continuous
  · apply continuous_sum_squares
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_apply 2
  · norm_num [squarePotential]

-- Multivariable Landscapes: Two paths disagree
Runner "MyGame" "MultivariableLandscapes" 5 (difficulty := 2) (inventory := []) := by
  rw [not_exists]
  intro L assumed
  have horizontal : PathLimit (fun t => pathRatio ![t,0,0]) 0 := by
    apply path_limit_of_values
    intro t ht
    rw [ratio_horizontal]
  have diagonal : PathLimit (fun t => pathRatio ![t,t,0]) (1/2) := by
    apply path_limit_of_values
    intro t ht
    rw [ratio_diagonal t ht]
  have first : (0 : ℝ) = L := path_limit_unique horizontal (limit_horizontal assumed)
  have second : (1/2 : ℝ) = L := path_limit_unique diagonal (limit_diagonal assumed)
  linarith

-- Multivariable Landscapes: Boss: repair the origin
Runner "MyGame" "MultivariableLandscapes" 6 (difficulty := 2) (inventory := []) := by
  apply continuous_fill_origin
  · apply continuous_sum_squares
    · exact continuous_apply 0
    · exact continuous_apply 1
    · exact continuous_apply 2
  · norm_num [squarePotential]

-- Partial Derivative Lab: Hold y fixed
Runner "MyGame" "PartialDerivativeLab" 1 (difficulty := 2) (inventory := []) := by
  rw [partialX, deriv_add_const, deriv_pow_field]
  norm_num

-- Partial Derivative Lab: Hold x fixed
Runner "MyGame" "PartialDerivativeLab" 2 (difficulty := 2) (inventory := []) := by
  rw [partialY, deriv_const_add, deriv_pow_field]
  ring

-- Partial Derivative Lab: Second derivatives
Runner "MyGame" "PartialDerivativeLab" 3 (difficulty := 2) (inventory := []) := by
  constructor
  · simp only [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
    norm_num
  · simp only [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id, deriv_const]

-- Partial Derivative Lab: Mixed partials agree
Runner "MyGame" "PartialDerivativeLab" 4 (difficulty := 2) (inventory := []) := by
  simp only [partialX, partialY, deriv_mul_const_field, deriv_const_mul_field]
  norm_num

-- Partial Derivative Lab: A tangent approximation
Runner "MyGame" "PartialDerivativeLab" 5 (difficulty := 2) (inventory := []) := by
  ring

-- Partial Derivative Lab: Boss: an implicit tangent plane
Runner "MyGame" "PartialDerivativeLab" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · rw [squarePotential]
    norm_num
  · constructor
    · rw [gradient_components]
      apply vector_eq
      · norm_num [partial_sum_squares]
      · norm_num [partial_sum_squares]
      · norm_num [partial_sum_squares]
    · constructor
      · apply vector_ne_zero 0
        norm_num
      · constructor
        · intro h
          norm_num [onPlane, dot] at h
          linarith
        · intro h
          norm_num [onPlane, dot, h]

-- Gradient Mountain: Assemble a gradient
Runner "MyGame" "GradientMountain" 1 (difficulty := 2) (inventory := []) := by
  rw [gradient_components]
  apply vector_eq
  · norm_num [partial_coordinate]
  · norm_num [partial_coordinate]
  · norm_num [partial_coordinate]

-- Gradient Mountain: A unit direction
Runner "MyGame" "GradientMountain" 2 (difficulty := 2) (inventory := []) := by
  rw [directional_coordinate]

-- Gradient Mountain: Along a parametrized path
Runner "MyGame" "GradientMountain" 3 (difficulty := 2) (inventory := []) := by
  have outer : HasDerivAt (fun s : ℝ => s^2) (2*(t^2)) (t^2) := by
    have rule := hasDerivAt_pow 2 (t^2)
    norm_num at rule
    exact rule
  have innerValue : HasDerivAt (fun s : ℝ => s^2) (2*t) t := by
    have rule := hasDerivAt_pow 2 t
    norm_num at rule
    exact rule
  apply derivative_value (derivative_chain (f := fun s : ℝ => s^2) (g := fun s : ℝ => s^2) outer innerValue)
  ring

-- Gradient Mountain: A Jacobian matrix
Runner "MyGame" "GradientMountain" 4 (difficulty := 2) (inventory := []) := by
  apply matrix_eq
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]
  · norm_num [jacobian, partial_coordinate, Matrix.one_apply]

-- Gradient Mountain: The ascent bound
Runner "MyGame" "GradientMountain" 5 (difficulty := 2) (inventory := []) := by
  have identity := ascent_squares u
  have perpendicular : 0 ≤ (4*u 0-3*u 1)^2 := sq_nonneg _
  have vertical : 0 ≤ (u 2)^2 := sq_nonneg _
  rw [hu] at identity
  have bound : (3*u 0+4*u 1)^2 ≤ (5:ℝ)^2 := by
    linarith
  have rate : 3*u 0+4*u 1 ≤ 5 := by
    apply le_of_sq_le_sq bound
    norm_num
  norm_num [dot]
  exact rate

-- Gradient Mountain: Boss: tangent to a level set
Runner "MyGame" "GradientMountain" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · simp [hv, hp]
  · rw [gradient_components]
    norm_num [dot, partial_coordinate, hv]

-- Optimization Arena: A critical point
Runner "MyGame" "OptimizationArena" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · intro h
    constructor
    · have first := h.1
      norm_num [partialX, deriv_add_const, deriv_pow_field] at first
      exact first
    · have second := h.2
      norm_num [partialY, deriv_const_add, deriv_pow_field] at second
      exact second
  · intro h
    constructor
    · norm_num [partialX, deriv_add_const, deriv_pow_field, h.1]
    · norm_num [partialY, deriv_const_add, deriv_pow_field, h.2]

-- Optimization Arena: Positive second variation
Runner "MyGame" "OptimizationArena" 2 (difficulty := 2) (inventory := []) := by
  constructor
  · constructor
    · norm_num [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
    · norm_num [partialX, partialY, deriv_add_const, deriv_const_add, deriv_pow_field, deriv_const_mul_id]
  · intro h k nonzero
    apply Or.elim nonzero
    · intro hh
      apply add_pos_of_pos_of_nonneg
      · exact sq_pos_of_ne_zero hh
      · exact sq_nonneg k
    · intro hk
      apply add_pos_of_nonneg_of_pos
      · exact sq_nonneg h
      · exact sq_pos_of_ne_zero hk

-- Optimization Arena: Saddle witnesses
Runner "MyGame" "OptimizationArena" 3 (difficulty := 2) (inventory := []) := by
  have positive : 0 < t^2 := sq_pos_of_ne_zero ht
  constructor
  · norm_num
    exact positive
  · norm_num
    linarith

-- Optimization Arena: Interior and boundary
Runner "MyGame" "OptimizationArena" 4 (difficulty := 2) (inventory := []) := by
  constructor
  · apply add_nonneg
    · exact sq_nonneg x
    · exact sq_nonneg y
  · exact h

-- Optimization Arena: Lagrange equations
Runner "MyGame" "OptimizationArena" 5 (difficulty := 2) (inventory := []) := by
  have multiplier : l ≠ 0 := by
    intro zero
    rw [zero] at hx
    norm_num at hx
  have same : l*(2*x) = l*(2*y) := by
    rw [← hx, ← hy]
  have twice : 2*x = 2*y := mul_left_cancel₀ multiplier same
  have equal : x = y := by linarith
  have square : x^2 = 1 := by
    rw [← equal] at hc
    linarith
  have factor : (x-1)*(x+1) = 0 := by
    have expansion : (x-1)*(x+1) = x^2-1 := by ring
    rw [expansion, square]
    norm_num
  apply Or.elim (mul_eq_zero.mp factor)
  · intro plus
    left
    have xvalue : x = 1 := by linarith
    constructor
    · exact xvalue
    · constructor
      · rw [← equal]
        exact xvalue
      · rw [xvalue] at hx
        linarith
  · intro minus
    right
    have xvalue : x = -1 := by linarith
    constructor
    · exact xvalue
    · constructor
      · rw [← equal]
        exact xvalue
      · rw [xvalue] at hx
        linarith

-- Optimization Arena: Boss: a global constrained optimum
Runner "MyGame" "OptimizationArena" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · constructor
    · norm_num
    · norm_num
  · intro x y feasible
    have identity : (x+y)^2+(x-y)^2 = 2*(x^2+y^2) := by ring
    rw [feasible] at identity
    have nonnegative : 0 ≤ (x-y)^2 := sq_nonneg _
    have squared : (x+y)^2 ≤ (2:ℝ)^2 := by linarith
    apply le_of_sq_le_sq squared
    norm_num

-- Double Integral Valley: A rectangle
Runner "MyGame" "DoubleIntegralValley" 1 (difficulty := 2) (inventory := []) := by
  have innerValue : (∫ y : ℝ in 0..3, (1:ℝ)) = 3 := by
    rw [constant_integral]
    norm_num
  rw [innerValue, constant_integral]
  norm_num

-- Double Integral Valley: A triangular region
Runner "MyGame" "DoubleIntegralValley" 2 (difficulty := 2) (inventory := []) := by
  constructor
  · intro bounds
    constructor
    · exact bounds.2.2.1
    · constructor
      · exact bounds.2.2.2
      · exact bounds.2.1
  · intro bounds
    constructor
    · exact le_trans bounds.1 bounds.2.1
    · constructor
      · exact bounds.2.2
      · constructor
        · exact bounds.1
        · exact bounds.2.1

-- Double Integral Valley: Reverse the order
Runner "MyGame" "DoubleIntegralValley" 3 (difficulty := 2) (inventory := []) := by
  have forward (x : ℝ) : (∫ y : ℝ in 0..x, (1:ℝ)) = x := by
    rw [constant_integral]
    ring
  have backward (y : ℝ) : (∫ x : ℝ in y..1, (1:ℝ)) = 1-y := by
    rw [constant_integral]
    ring
  rw [integral_values forward, integral_values backward]
  rw [intervalIntegral.integral_sub (f := fun _ : ℝ => (1:ℝ)) (g := fun y : ℝ => y) (continuous_const.intervalIntegrable 0 1) (continuous_id.intervalIntegrable 0 1)]
  norm_num [integral_id]

-- Double Integral Valley: Area and volume
Runner "MyGame" "DoubleIntegralValley" 4 (difficulty := 2) (inventory := []) := by
  constructor
  · rw [constant_integral, constant_integral]
    norm_num
  · rw [constant_integral, constant_integral]
    norm_num

-- Double Integral Valley: A lamina centroid
Runner "MyGame" "DoubleIntegralValley" 5 (difficulty := 2) (inventory := []) := by
  constructor
  · norm_num [constant_integral]
  · constructor
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..1, x) = x := by
        rw [constant_integral]
        ring
      rw [integral_values innerValue, integral_id]
      norm_num
    · have innerValue : (∫ y : ℝ in 0..1, y) = 1/2 := by
        rw [integral_id]
        norm_num
      rw [innerValue, constant_integral]
      norm_num

-- Double Integral Valley: Boss: a triangular lamina
Runner "MyGame" "DoubleIntegralValley" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, (1:ℝ)) = x := by
      rw [constant_integral]
      ring
    rw [integral_values innerValue, integral_id]
    norm_num
  · constructor
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, x) = x^2 := by
        rw [constant_integral]
        ring
      rw [integral_values innerValue, integral_pow]
      norm_num
    · have innerValue (x : ℝ) : (∫ y : ℝ in 0..x, y) = x^2/2 := by
        rw [integral_id]
        ring
      rw [integral_values innerValue, intervalIntegral.integral_div, integral_pow]
      norm_num

-- Triple Integral Caverns: A rectangular box
Runner "MyGame" "TripleIntegralCaverns" 1 (difficulty := 2) (inventory := []) := by
  have innerValue : (∫ z : ℝ in 0..4, (1:ℝ)) = 4 := by
    rw [constant_integral]
    norm_num
  have middle : (∫ y : ℝ in 0..3, (4:ℝ)) = 12 := by
    rw [constant_integral]
    norm_num
  rw [innerValue, middle, constant_integral]
  norm_num

-- Triple Integral Caverns: Bounds for a solid
Runner "MyGame" "TripleIntegralCaverns" 2 (difficulty := 2) (inventory := []) := by
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

-- Triple Integral Caverns: Volume below a roof
Runner "MyGame" "TripleIntegralCaverns" 3 (difficulty := 2) (inventory := []) := by
  have innerValue (x : ℝ) : (∫ z : ℝ in 0..x, (1:ℝ)) = x := by
    rw [constant_integral]
    ring
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..x, (1:ℝ)) = x := by
    rw [innerValue, constant_integral]
    ring
  rw [integral_values crossSection, integral_id]
  norm_num

-- Triple Integral Caverns: Variable density
Runner "MyGame" "TripleIntegralCaverns" 4 (difficulty := 2) (inventory := []) := by
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x^2) = x^2 := by
    rw [constant_integral, constant_integral]
    ring
  rw [integral_values crossSection, integral_pow]
  norm_num

-- Triple Integral Caverns: A first moment
Runner "MyGame" "TripleIntegralCaverns" 5 (difficulty := 2) (inventory := []) := by
  have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x*x^2) = x^3 := by
    rw [constant_integral, constant_integral]
    ring
  rw [integral_values crossSection, integral_pow]
  norm_num

-- Triple Integral Caverns: Boss: the center of a solid
Runner "MyGame" "TripleIntegralCaverns" 6 (difficulty := 2) (inventory := []) := by
  constructor
  · norm_num [constant_integral]
  · constructor
    · have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, x) = x := by
        rw [constant_integral, constant_integral]
        ring
      rw [integral_values crossSection, integral_id]
      norm_num
    · constructor
      · have innerValue (y : ℝ) : (∫ z : ℝ in 0..1, y) = y := by
          rw [constant_integral]
          ring
        have crossSection (x : ℝ) : (∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, y) = 1/2 := by
          rw [integral_values innerValue, integral_id]
          norm_num
        rw [integral_values crossSection, constant_integral]
        norm_num
      · have innerValue : (∫ z : ℝ in 0..1, z) = 1/2 := by
          rw [integral_id]
          norm_num
        rw [innerValue, constant_integral, constant_integral]
        norm_num

-- Coordinate Portal: Polar identities
Runner "MyGame" "CoordinatePortal" 1 (difficulty := 2) (inventory := []) := by
  have factor : (r*Real.cos t)^2+(r*Real.sin t)^2 = r^2*(Real.sin t^2+Real.cos t^2) := by ring
  rw [factor, Real.sin_sq_add_cos_sq]
  ring

-- Coordinate Portal: Polar area factor
Runner "MyGame" "CoordinatePortal" 2 (difficulty := 2) (inventory := []) := by
  have determinant : Matrix.det (planarJacobian polarX polarY r t) = r := by
    norm_num [planarJacobian, polarX, polarY, partialX, partialY, Matrix.det_fin_two, deriv_mul_const_field, deriv_const_mul_field]
    apply Eq.trans (b := r*(Real.sin t^2+Real.cos t^2))
    · ring
    · rw [Real.sin_sq_add_cos_sq]
      ring
  constructor
  · rw [determinant, abs_of_nonneg hr]
  · have radial : (∫ r : ℝ in 0..1, r) = 1/2 := by
      rw [integral_id]
      norm_num
    rw [radial, constant_integral]
    ring

-- Coordinate Portal: Cylindrical volume
Runner "MyGame" "CoordinatePortal" 3 (difficulty := 2) (inventory := []) := by
  have vertical (r : ℝ) : (∫ z : ℝ in 0..2, r) = 2*r := by
    rw [constant_integral]
    ring
  have radial : (∫ r : ℝ in 0..1, ∫ z : ℝ in 0..2, r) = 1 := by
    rw [integral_values vertical, intervalIntegral.integral_const_mul, integral_id]
    norm_num
  rw [radial, constant_integral]
  ring

-- Coordinate Portal: Spherical volume
Runner "MyGame" "CoordinatePortal" 4 (difficulty := 2) (inventory := []) := by
  constructor
  · intro r p lower upper
    apply abs_of_nonneg
    apply mul_nonneg
    · exact sq_nonneg r
    · apply Real.sin_nonneg_of_mem_Icc
      constructor
      · exact lower
      · exact upper
  · have radial (p : ℝ) : (∫ r : ℝ in 0..1, r^2*Real.sin p) = (1/3)*Real.sin p := by
      rw [intervalIntegral.integral_mul_const, integral_pow]
      norm_num
    have polar : (∫ p : ℝ in 0..Real.pi, ∫ r : ℝ in 0..1, r^2*Real.sin p) = 2/3 := by
      rw [integral_values radial, intervalIntegral.integral_const_mul, integral_sin]
      norm_num
    rw [polar, constant_integral]
    ring

-- Coordinate Portal: A nonpolar Jacobian
Runner "MyGame" "CoordinatePortal" 5 (difficulty := 2) (inventory := []) := by
  have determinant : Matrix.det (planarJacobian (fun u _ => 2*u) (fun _ v => -3*v) 0 0) = -6 := by
    norm_num [planarJacobian, partialX, partialY, Matrix.det_fin_two, deriv_const_mul_id]
  constructor
  · exact determinant
  · rw [determinant]
    norm_num

-- Coordinate Portal: Boss: an absolute Jacobian
Runner "MyGame" "CoordinatePortal" 6 (difficulty := 2) (inventory := []) := by
  have determinant : |Matrix.det (!![(2:ℝ),0;0,-3])| = 6 := by
    norm_num [Matrix.det_fin_two]
  have original : (∫ x : ℝ in 0..2, ∫ y : ℝ in (-3)..0, (1:ℝ)) = 6 := by
    norm_num [constant_integral]
  rw [original, determinant]
  norm_num [constant_integral]

-- Vector Field Observatory: Compare two fields
Runner "MyGame" "VectorFieldObservatory" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · rfl
  · apply vector_eq
    · norm_num [rotation]
    · norm_num [rotation]
    · norm_num [rotation]

-- Vector Field Observatory: Recognize a gradient
Runner "MyGame" "VectorFieldObservatory" 2 (difficulty := 2) (inventory := []) := by
  rw [gradient_components]
  apply vector_eq
  · norm_num [partial_xy]
  · norm_num [partial_xy]
  · norm_num [partial_xy]

-- Vector Field Observatory: Divergence
Runner "MyGame" "VectorFieldObservatory" 3 (difficulty := 2) (inventory := []) := by
  rw [divergence]
  norm_num [radial, partial_coordinate]

-- Vector Field Observatory: Curl
Runner "MyGame" "VectorFieldObservatory" 4 (difficulty := 2) (inventory := []) := by
  rw [curl]
  apply vector_eq
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]
  · norm_num [rotation, partial_div_const, partial_neg, partial_coordinate, partial_constant]

-- Vector Field Observatory: Two differential identities
Runner "MyGame" "VectorFieldObservatory" 5 (difficulty := 2) (inventory := []) := by
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

-- Vector Field Observatory: Boss: construct a potential
Runner "MyGame" "VectorFieldObservatory" 6 (difficulty := 2) (inventory := []) := by
  use fun q => q 0*q 1
  constructor
  · norm_num
  · intro p
    rw [gradient_components]
    apply vector_eq
    · norm_num [partial_xy]
    · norm_num [partial_xy]
    · norm_num [partial_xy]

-- Path Integral Trails: Choose an orientation
Runner "MyGame" "PathIntegralTrails" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · simp
  · simp

-- Path Integral Trails: A weighted wire
Runner "MyGame" "PathIntegralTrails" 2 (difficulty := 2) (inventory := []) := by
  have integrand (t : ℝ) : (fun p : Vec => p 0) ![t,0,0] * speed (fun s => ![s,0,0]) t = t := by
    rw [speed, velocity_components]
    norm_num [length, lengthSq, dot]
  rw [scalarLineIntegral, integral_values integrand, integral_id]
  norm_num

-- Path Integral Trails: Work along a curve
Runner "MyGame" "PathIntegralTrails" 3 (difficulty := 2) (inventory := []) := by
  have integrand (t : ℝ) : dot ((fun p : Vec => ![p 0,0,0]) ![t,0,0]) (velocity (fun s => ![s,0,0]) t) = t := by
    rw [velocity_components, dot]
    norm_num
  rw [work, integral_values integrand, integral_id]
  norm_num

-- Path Integral Trails: Reverse orientation
Runner "MyGame" "PathIntegralTrails" 4 (difficulty := 2) (inventory := []) := by
  rw [work, work]
  apply reverse_integral

-- Path Integral Trails: Apply the endpoint theorem
Runner "MyGame" "PathIntegralTrails" 5 (difficulty := 2) (inventory := []) := by
  apply work_eq_endpoint
  · exact hc
  · exact hi

-- Path Integral Trails: Boss: path independence
Runner "MyGame" "PathIntegralTrails" 6 (difficulty := 2) (inventory := []) := by
  have first := work_first_coordinate c 0 1 hc hic
  have second := work_first_coordinate d 0 1 hd hid
  constructor
  · exact first
  · rw [first, second, h0, h1]

-- Green’s Garden: A positive boundary
Runner "MyGame" "GreensGarden" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  · apply vector_eq
    · norm_num
    · norm_num
    · norm_num

-- Green’s Garden: Circulation by edges
Runner "MyGame" "GreensGarden" 2 (difficulty := 2) (inventory := []) := by
  have edge1 : work (fun p => ![0,p 0,0]) (fun t => ![t,0,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge2 : work (fun p => ![0,p 0,0]) (fun t => ![1,t,0]) 0 1 = 1 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge3 : work (fun p => ![0,p 0,0]) (fun t => ![1-t,1,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge4 : work (fun p => ![0,p 0,0]) (fun t => ![0,1-t,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  rw [squareCirculation, edge1, edge2, edge3, edge4]
  norm_num

-- Green’s Garden: The interior integrand
Runner "MyGame" "GreensGarden" 3 (difficulty := 2) (inventory := []) := by
  have integrand (x y : ℝ) : (curl (fun p => ![0,p 0,0]) ![x,y,0]) 2 = 1 := by
    rw [curl]
    norm_num [partial_coordinate, partial_constant]
  have innerValue (x : ℝ) : (∫ y : ℝ in 0..1, (curl (fun p => ![0,p 0,0]) ![x,y,0]) 2) = 1 := by
    rw [integral_values (integrand x), constant_integral]
    norm_num
  rw [integral_values innerValue, constant_integral]
  norm_num

-- Green’s Garden: Green for a shear field
Runner "MyGame" "GreensGarden" 4 (difficulty := 2) (inventory := []) := by
  apply green_shear

-- Green’s Garden: Green in flux form
Runner "MyGame" "GreensGarden" 5 (difficulty := 2) (inventory := []) := by
  have boundary : squareOutwardFlux (fun p => ![p 0,p 1,0]) = 2 := by
    rw [squareOutwardFlux]
    norm_num [dot]
  have insideValue : (∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, divergence (fun p => ![p 0,p 1,0]) ![x,y,0]) = 2 := by
    norm_num [divergence, partial_coordinate, partial_constant]
  rw [boundary, insideValue]

-- Green’s Garden: Boss: area from the boundary
Runner "MyGame" "GreensGarden" 6 (difficulty := 2) (inventory := []) := by
  have circulation : squareCirculation rotation = 1 := by
    have edge1 : work (rotation) (fun t => ![t,0,0]) 0 1 = 0 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge2 : work (rotation) (fun t => ![1,t,0]) 0 1 = 1/2 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge3 : work (rotation) (fun t => ![1-t,1,0]) 0 1 = 1/2 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    have edge4 : work (rotation) (fun t => ![0,1-t,0]) 0 1 = 0 := by
      norm_num [work, dot, velocity_components, deriv_const_sub_id, rotation]
    rw [squareCirculation, edge1, edge2, edge3, edge4]
    norm_num
  constructor
  · rw [circulation]
    norm_num [constant_integral]
  · exact circulation

-- Surface Expedition: Parametrize a surface
Runner "MyGame" "SurfaceExpedition" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · rfl
  · constructor
    · rfl
    · rfl

-- Surface Expedition: Tangents and normal
Runner "MyGame" "SurfaceExpedition" 2 (difficulty := 2) (inventory := []) := by
  have du : velocity (fun t => patch t v) u = (![1,0,0] : Vec) := by
    simp only [patch, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  have dv : velocity (patch u) v = (![0,1,0] : Vec) := by
    have coordinates (t : ℝ) : patch u t = (![u,t,0] : Vec) := by rfl
    rw [velocity_congr coordinates, velocity_components]
    apply vector_eq
    · norm_num
    · norm_num
    · norm_num
  constructor
  · exact du
  · constructor
    · exact dv
    · rw [surfaceNormal, du, dv]
      apply vector_eq
      · norm_num [cross]
      · norm_num [cross]
      · norm_num [cross]

-- Surface Expedition: Area factor
Runner "MyGame" "SurfaceExpedition" 3 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  rw [normal]
  norm_num [length, lengthSq, dot]

-- Surface Expedition: A scalar surface integral
Runner "MyGame" "SurfaceExpedition" 4 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have innerValue (u : ℝ) : (∫ v : ℝ in 0..1, (fun p : Vec => p 0) (patch u v) * length (surfaceNormal patch u v)) = u := by
    norm_num [normal, patch, length, lengthSq, dot, constant_integral]
  rw [surfaceIntegral, integral_values innerValue, integral_id]
  norm_num

-- Surface Expedition: Oriented flux
Runner "MyGame" "SurfaceExpedition" 5 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have innerValue (u : ℝ) : (∫ v : ℝ in 0..1, dot (![0,0,1] : Vec) (surfaceNormal patch u v)) = 1 := by
    norm_num [normal, dot, constant_integral]
  rw [surfaceFlux, integral_values innerValue, constant_integral]
  norm_num

-- Surface Expedition: Boss: reverse the patch
Runner "MyGame" "SurfaceExpedition" 6 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have reversed (u v : ℝ) : surfaceNormal (fun s t => ![t,s,0]) u v = (![0,0,-1] : Vec) := by
    rw [normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  have upFlux : surfaceFlux (fun _ => ![0,0,1]) patch 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, normal, dot]
  have downFlux : surfaceFlux (fun _ => ![0,0,1]) (fun u v => ![v,u,0]) 0 1 0 1 = -1 := by
    norm_num [surfaceFlux, reversed, dot]
  have upArea : surfaceIntegral (fun _ => 1) patch 0 1 0 1 = 1 := by
    norm_num [surfaceIntegral, normal, length, lengthSq, dot]
  have downArea : surfaceIntegral (fun _ => 1) (fun u v => ![v,u,0]) 0 1 0 1 = 1 := by
    norm_num [surfaceIntegral, reversed, length, lengthSq, dot]
  constructor
  · rw [downFlux, upFlux]
  · rw [downArea, upArea]

-- Stokes Summit: The boundary of a patch
Runner "MyGame" "StokesSummit" 1 (difficulty := 2) (inventory := []) := by
  constructor
  · rfl
  · constructor
    · rfl
    · constructor
      · rfl
      · rfl

-- Stokes Summit: Match orientations
Runner "MyGame" "StokesSummit" 2 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  constructor
  · exact normal 0 0
  · simp only [patch, velocity_components]
    apply vector_eq
    · norm_num [deriv_const_sub_id]
    · norm_num [deriv_const_sub_id]
    · norm_num [deriv_const_sub_id]

-- Stokes Summit: Curl through a patch
Runner "MyGame" "StokesSummit" 3 (difficulty := 2) (inventory := []) := by
  have normal (s t : ℝ) : surfaceNormal patch s t = (![0,0,1] : Vec) := by
    have coordinates (a b : ℝ) : patch a b = (![a,b,0] : Vec) := by rfl
    rw [normal_congr coordinates, normal_components]
    apply vector_eq
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
    · norm_num [partialX, partialY, cross]
  rw [normal, curl, dot]
  norm_num [partial_coordinate, partial_constant]

-- Stokes Summit: The boundary calculation
Runner "MyGame" "StokesSummit" 4 (difficulty := 2) (inventory := []) := by
  have edge1 : work (fun p => ![0,2*p 0,0]) (fun t => ![t,0,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge2 : work (fun p => ![0,2*p 0,0]) (fun t => ![1,t,0]) 0 1 = 2 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge3 : work (fun p => ![0,2*p 0,0]) (fun t => ![1-t,1,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  have edge4 : work (fun p => ![0,2*p 0,0]) (fun t => ![0,1-t,0]) 0 1 = 0 := by
    norm_num [work, dot, velocity_components, deriv_const_sub_id]
  rw [squareCirculation, edge1, edge2, edge3, edge4]
  norm_num

-- Stokes Summit: Apply Stokes: square patch
Runner "MyGame" "StokesSummit" 5 (difficulty := 2) (inventory := []) := by
  apply stokes_shear_patch

-- Stokes Summit: Boss: choose a simpler surface
Runner "MyGame" "StokesSummit" 6 (difficulty := 2) (inventory := []) := by
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

-- Gauss Citadel: An outward closed boundary
Runner "MyGame" "GaussCitadel" 1 (difficulty := 2) (inventory := []) := by
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

-- Gauss Citadel: Divergence in the solid
Runner "MyGame" "GaussCitadel" 2 (difficulty := 2) (inventory := []) := by
  have div (p : Vec) : divergence radial p = 3 := by
    rw [divergence]
    norm_num [radial, partial_coordinate]
  norm_num [div, constant_integral]

-- Gauss Citadel: Flux by boundary pieces
Runner "MyGame" "GaussCitadel" 3 (difficulty := 2) (inventory := []) := by
  have face1 : surfaceFlux radial (fun s t => ![1,s,t]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face2 : surfaceFlux radial (fun s t => ![0,t,s]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face3 : surfaceFlux radial (fun s t => ![t,1,s]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face4 : surfaceFlux radial (fun s t => ![s,0,t]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face5 : surfaceFlux radial (fun s t => ![s,t,1]) 0 1 0 1 = 1 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  have face6 : surfaceFlux radial (fun s t => ![t,s,0]) 0 1 0 1 = 0 := by
    norm_num [surfaceFlux, radial, normal_components, partialX, partialY, cross, dot]
  rw [cubeFlux, face1, face2, face3, face4, face5, face6]
  norm_num

-- Gauss Citadel: Apply Gauss on a cube
Runner "MyGame" "GaussCitadel" 4 (difficulty := 2) (inventory := []) := by
  apply gauss_diagonal

-- Gauss Citadel: Recover a missing face
Runner "MyGame" "GaussCitadel" 5 (difficulty := 2) (inventory := []) := by
  have total : cubeFlux (fun p => ![2*p 0,3*p 1,4*p 2]) = 9 := by
    rw [gauss_diagonal]
    norm_num [divergence_diagonal]
  rw [total] at h
  linarith

-- Gauss Citadel: Final boss: three integral bridges
Runner "MyGame" "GaussCitadel" 6 (difficulty := 2) (inventory := []) := by
  have gauss : cubeFlux radial = ∫ x : ℝ in 0..1, ∫ y : ℝ in 0..1, ∫ z : ℝ in 0..1, divergence radial ![x,y,z] := by
    have rule := gauss_diagonal 1 1 1
    simp only [one_mul, vector_components] at rule
    exact rule
  constructor
  · apply green_shear
  · constructor
    · apply stokes_shear_patch
    · constructor
      · exact gauss
      · have circulation : squareCirculation (fun p => ![0,2*p 0,0]) = 2 := by
          rw [green_shear]
          norm_num [curl, partial_scaled_coordinate, partial_constant]
        have flux : cubeFlux radial = 3 := by
          rw [gauss]
          norm_num [divergence, radial, partial_coordinate]
        rw [circulation, flux]
        norm_num
