import NlsGge.GK38.ActionEllipseContinuity

set_option autoImplicit false
open Set MeasureTheory
open scoped ComplexConjugate
namespace NlsGge.GK38.ActionEllipseReflection
noncomputable section

def pullback (f : ℂ → ℂ) (c r δ θ : ℝ) : ℂ :=
  NlsGge.Analysis.EllipseDeformation.velocity r δ θ * f (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r δ θ)

theorem curve_reflection (c r δ θ : ℝ) :
    NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r δ (2 * Real.pi - θ) =
      conj (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r δ θ) := by
  simp only [NlsGge.Analysis.EllipseDeformation.curve, Real.cos_two_pi_sub, Real.sin_two_pi_sub,
    map_add, map_mul, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem velocity_reflection (r δ θ : ℝ) :
    NlsGge.Analysis.EllipseDeformation.velocity r δ (2 * Real.pi - θ) =
      -conj (NlsGge.Analysis.EllipseDeformation.velocity r δ θ) := by
  simp only [NlsGge.Analysis.EllipseDeformation.velocity, Real.cos_two_pi_sub, Real.sin_two_pi_sub,
    map_add, map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
  ring

theorem pullback_reflection {f : ℂ → ℂ} (c r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hf : ∀ z : ℂ, z.im ≠ 0 → f (conj z) = -conj (f z))
    {θ : ℝ} (hθ : θ ∈ Ioo (0 : ℝ) Real.pi) :
    pullback f c r δ (2 * Real.pi - θ) = conj (pullback f c r δ θ) := by
  have hi : (NlsGge.Analysis.EllipseDeformation.curve (c : ℂ) r δ θ).im ≠ 0 := by
    rw [NlsGge.GK38.ActionEllipseDomain.curve_im _ _ _ _ (by simp)]
    exact ne_of_gt (mul_pos (mul_pos hδ hr) (Real.sin_pos_of_pos_of_lt_pi hθ.1 hθ.2))
  simp only [pullback, curve_reflection, velocity_reflection, hf _ hi, neg_mul_neg, map_mul]

theorem lower_integral_eq_conj_upper {f : ℂ → ℂ} (c r δ : ℝ) (hr : 0 < r) (hδ : 0 < δ)
    (hf : ∀ z : ℂ, z.im ≠ 0 → f (conj z) = -conj (f z)) :
    (∫ θ in Real.pi..2 * Real.pi, pullback f c r δ θ) =
      conj (∫ θ in (0 : ℝ)..Real.pi, pullback f c r δ θ) := by
  have he := intervalIntegral.integral_comp_sub_left (pullback f c r δ)
    (a := (0 : ℝ)) (b := Real.pi) (2 * Real.pi)
  have hp : 2 * Real.pi - Real.pi = Real.pi := by ring
  rw [hp, sub_zero] at he
  rw [← he, ← intervalIntegral.intervalIntegral_conj]
  apply intervalIntegral.integral_congr_Ioo_of_le Real.pi_pos.le
  intro θ hθ
  exact pullback_reflection c r δ hr hδ hf hθ

theorem full_integral_eq_upper_add_conj {f : ℂ → ℂ} (c r δ : ℝ)
    (hr : 0 < r) (hδ : 0 < δ)
    (hf : ∀ z : ℂ, z.im ≠ 0 → f (conj z) = -conj (f z))
    (hi : IntervalIntegrable (pullback f c r δ) volume 0 (2 * Real.pi)) :
    (∫ θ in (0 : ℝ)..2 * Real.pi, pullback f c r δ θ) =
      (∫ θ in (0 : ℝ)..Real.pi, pullback f c r δ θ) +
        conj (∫ θ in (0 : ℝ)..Real.pi, pullback f c r δ θ) := by
  have hl : IntervalIntegrable (pullback f c r δ) volume 0 Real.pi := by
    apply hi.mono_set
    rw [uIcc_of_le Real.pi_pos.le, uIcc_of_le Real.two_pi_pos.le]
    exact Icc_subset_Icc le_rfl (by linarith [Real.pi_pos])
  have hu : IntervalIntegrable (pullback f c r δ) volume Real.pi (2 * Real.pi) := by
    apply hi.mono_set
    rw [uIcc_of_le (by linarith [Real.pi_pos] : Real.pi ≤ 2 * Real.pi),
      uIcc_of_le Real.two_pi_pos.le]
    exact Icc_subset_Icc Real.pi_pos.le le_rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals hl hu,
    lower_integral_eq_conj_upper c r δ hr hδ hf]

end
end NlsGge.GK38.ActionEllipseReflection
