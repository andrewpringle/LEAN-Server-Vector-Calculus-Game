import Game.Calculus

noncomputable section
namespace VectorCalculus

/-- The columns are the two parameter derivatives, not supplied answer data. -/
def planarJacobian (x y : ℝ → ℝ → ℝ) (u v : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![partialX x u v, partialY x u v; partialX y u v, partialY y u v]

def polarX (r t : ℝ) : ℝ := r * Real.cos t
def polarY (r t : ℝ) : ℝ := r * Real.sin t

end VectorCalculus
