import QuantumNLS.Ext025A7InverseBounds

/-! LOCAL-009's derivative constants, uniform in the spectral parameter and
label, from the exact source inequalities. The geometric proof of those
source inequalities and operator functional calculus are separate clauses. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A7

theorem spectralLinear_norm (κ L : ℝ) (z : ℂ) :
    ‖spectralLinear κ L z‖ = |κ| * ‖1 - Complex.exp (Complex.I * z * L)‖ := by
  simp [spectralLinear]

/-- Fixed numerical source margins give a uniform lower slope and target
value bound throughout the full selected inverse disk. -/
theorem local009_source_constants {κ L R : ℝ} {z y : ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hsmall : κ * R ≤ 1)
    (hexp : ‖Complex.exp (Complex.I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (Complex.I * z * L)‖)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    κ / 2 ≤ ‖spectralLinear κ L z‖ ∧ ‖y‖ ≤ 16 := by
  have hnorm := spectralLinear_norm κ L z
  rw [abs_of_pos hκ] at hnorm
  have hDlo : κ / 2 ≤ ‖spectralLinear κ L z‖ := by nlinarith
  have hgapup : ‖1 - Complex.exp (Complex.I * z * L)‖ ≤ 9 := by
    have := norm_sub_le (1 : ℂ) (Complex.exp (Complex.I * z * L))
    norm_num at this
    linarith
  have hDup : ‖spectralLinear κ L z‖ ≤ 9 * κ := by nlinarith
  have hf0 : ‖spectralMap κ L z 0‖ ≤ 9 := by
    have hsum : 1 + ‖Complex.exp (Complex.I * z * L)‖ ≤ 9 := by linarith
    simpa [spectralMap] using (norm_add_le (1 : ℂ)
      (Complex.exp (Complex.I * z * L))).trans (by simpa using hsum)
  have hyt : ‖y‖ ≤ ‖y - spectralMap κ L z 0‖ + ‖spectralMap κ L z 0‖ :=
    norm_le_norm_sub_add _ _
  constructor
  · exact hDlo
  · have hm := mul_le_mul_of_nonneg_right hDup hR.le
    nlinarith

/-- Both scalar inverse derivative bounds depend only on kappa; all
spectral points in U use the same full source/target disk margins. -/
theorem local009_uniform_inverse_bounds (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hsmall : κ * R ≤ 1) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (Complex.I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (Complex.I * z * L)‖)
    (hb : ∀ z ∈ U, ∀ v ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z v - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    ‖deriv (spectralInverse κ L R z) y‖ ≤ (3 * κ / 8)⁻¹ ∧
      ‖deriv (deriv (spectralInverse κ L R z)) y‖ ≤
        κ^2 * 16 / (3 * κ / 8)^3 := by
  have hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0 := by
    intro v hv
    rw [← norm_pos_iff, spectralLinear_norm, abs_of_pos hκ]
    exact mul_pos hκ ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hgap v hv))
  obtain ⟨hlo, hyb⟩ := local009_source_constants hκ hR hsmall (hexp z hz) (hgap z hz) hy
  constructor
  · exact (local009_inverse_derivative_bound κ L hR hU hD hb hz hy).trans
      (inv_anti₀ (by positivity) (by linarith))
  · apply (local009_inverse_second_bound κ L hR hU hD hb hz hy).trans
    rw [abs_of_pos hκ]
    gcongr
    linarith
end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.spectralLinear_norm
#print axioms QuantumNLS.Ext025A7.local009_source_constants
#print axioms QuantumNLS.Ext025A7.local009_uniform_inverse_bounds
