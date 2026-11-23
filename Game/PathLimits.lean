import Game.Calculus

noncomputable section
namespace VectorCalculus
open Filter
open scoped Topology

/-- The value at the origin is defined by real division, but does not repair the limit. -/
def pathRatio (p : Vec) : ℝ := p 0 * p 1 / (p 0 ^ 2 + p 1 ^ 2)

/-- The horizontal path is constantly zero. -/
theorem ratio_horizontal (t : ℝ) : pathRatio ![t,0,0] = 0 := by
  simp [pathRatio]

/-- The nonzero part of the diagonal path is constantly one half. -/
theorem ratio_diagonal (t : ℝ) (ht : t ≠ 0) : pathRatio ![t,t,0] = 1/2 := by
  simp only [pathRatio, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hden : t^2+t^2 ≠ 0 := by nlinarith [sq_pos_of_ne_zero ht]
  field_simp
  <;> nlinarith [sq_pos_of_ne_zero ht]

theorem ratio_diagonal_limit :
    Tendsto (fun t : ℝ => pathRatio ![t,t,0]) (𝓝[≠] 0) (𝓝 (1/2)) := by
  apply Tendsto.congr' (f₁ := fun _ : ℝ => (1/2 : ℝ)) ?_ tendsto_const_nhds
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (ratio_diagonal t ht).symm

/-- Nonzero t gives a nonzero point, so this path genuinely approaches the
punctured origin rather than staying at the exceptional point. -/
theorem coordinatePath_tendsto (d : ℝ) :
    Tendsto (fun t : ℝ => (![t,d*t,0] : Vec)) (𝓝[≠] 0) (𝓝[≠] (0 : Vec)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · have hc : Continuous (fun t : ℝ => (![t,d*t,0] : Vec)) := by fun_prop
    have hz : (fun t : ℝ => (![t,d*t,0] : Vec)) 0 = (0 : Vec) := by
      funext i; fin_cases i <;> norm_num
    simpa only [hz] using (hc.tendsto 0).mono_left
      (show (𝓝[≠] (0:ℝ)) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  · filter_upwards [self_mem_nhdsWithin] with t ht
    change (![t,d*t,0] : Vec) ≠ 0
    intro h
    have hh := congrFun h 0
    simp only [Matrix.cons_val_zero, Pi.zero_apply] at hh
    exact ht hh

end VectorCalculus
