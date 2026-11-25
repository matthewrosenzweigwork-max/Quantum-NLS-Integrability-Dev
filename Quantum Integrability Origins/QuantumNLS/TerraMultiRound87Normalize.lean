import Mathlib

/-! Normalization of an orthogonal projection: a geometric helper for the
spectral Markov step. The energy estimate and Pythagorean identity must be
proved separately for the actual physical projection. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound87Normalize

/-- If `p` is the orthogonal part of the unit vector `v`, normalizing `p`
costs at most twice the length of the discarded component. -/
theorem normalize_projection {H : Type*} [NormedAddCommGroup H]
    [NormedSpace ℝ H] (v p : H) (hv : ‖v‖ = 1) (hp : 0 < ‖p‖)
    (hpyth : ‖v‖ ^ 2 = ‖p‖ ^ 2 + ‖v - p‖ ^ 2) :
    ‖(‖p‖⁻¹ : ℝ) • p‖ = 1 ∧
      ‖v - (‖p‖⁻¹ : ℝ) • p‖ ≤ 2 * ‖v - p‖ := by
  have hp1 : ‖p‖ ≤ 1 := by nlinarith [sq_nonneg ‖v - p‖, norm_nonneg p]
  have hq : 1 - ‖p‖ ≤ ‖v - p‖ := by
    have hq0 := norm_nonneg (v - p)
    have ha := mul_nonneg hp.le (sub_nonneg.mpr hp1)
    nlinarith [sq_nonneg (‖p‖ - 1), sq_nonneg (‖v - p‖), hv]
  have hunit : ‖(‖p‖⁻¹ : ℝ) • p‖ = 1 := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hp), inv_mul_cancel₀ hp.ne']
  have hpdist : ‖p - (‖p‖⁻¹ : ℝ) • p‖ = 1 - ‖p‖ := by
    have he : p - (‖p‖⁻¹ : ℝ) • p = (1 - ‖p‖⁻¹ : ℝ) • p := by module
    rw [he, norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (one_le_inv₀ hp |>.2 hp1))]
    field_simp
    ring
  refine ⟨hunit, ?_⟩
  have ht := dist_triangle v p ((‖p‖⁻¹ : ℝ) • p)
  rw [dist_eq_norm, dist_eq_norm, dist_eq_norm, hpdist] at ht
  linarith

#print axioms normalize_projection
end QuantumNLS.TerraMultiRound87Normalize
