import NlsGge.GK38.DirichletRealAlgebra

/-! Scalar Green endpoint and quotient adapters, independent of fund unfolding. -/
set_option autoImplicit false
namespace NlsGge.GK38

/-- Endpoint Green identity gives the exact Dirichlet difference quotient. -/
theorem dirichletGreen_scalar_factor38 (α a b w J : ℂ)
    (h : α * b - α * a = Complex.I * w * J) :
    ((b - a) / (2 * Complex.I)) * α = w * J / 2 := by
  calc
    _ = (α * b - α * a) / (2 * Complex.I) := by ring
    _ = (Complex.I * w * J) / (2 * Complex.I) := by rw [h]
    _ = _ := by field_simp


/-- Cancellation is only used away from the base spectral parameter. -/
theorem dirichletGreen_scalar_quotient38 (f α w J : ℂ) (hw : w ≠ 0)
    (h : f * α = w * J / 2) : w⁻¹ * f * α = J / 2 := by
  calc
    _ = w⁻¹ * (f * α) := by ring
    _ = w⁻¹ * (w * J / 2) := by rw [h]
    _ = _ := by field_simp

end NlsGge.GK38
