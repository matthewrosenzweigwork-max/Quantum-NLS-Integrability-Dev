import Mathlib
import NlsGge.GK38.PairPotential

/-!
# F5: uniform complex-frequency oscillatory estimates

GK Appendix D.1. Smooth approximation in the interval L1 norm and integration
by parts give decay uniformly in time and in the full complex spectral plane.
-/

set_option autoImplicit false

open Filter Topology MeasureTheory Set

namespace NlsGge.GK38

noncomputable section

theorem norm_osc_exp_le (z : ℂ) {t s : ℝ} (_ht : 0 ≤ t) (hs : s ∈ Icc 0 t) :
    ‖Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s))‖ ≤ Real.exp (|z.im| * t) := by
  have habs : |t - 2 * s| ≤ t := abs_le.mpr ⟨by linarith [hs.2], by linarith [hs.1]⟩
  have hmul : -(z.im * (t - 2 * s)) ≤ |z.im| * t := by
    calc -(z.im * (t - 2 * s)) ≤ |z.im * (t - 2 * s)| := neg_le_abs _
      _ = |z.im| * |t - 2 * s| := abs_mul _ _
      _ ≤ |z.im| * t := mul_le_mul_of_nonneg_left habs (abs_nonneg _)
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  simpa [Complex.mul_re, Complex.mul_im] using hmul

theorem intervalIntegrable_osc (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 1)
    (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    IntervalIntegrable (fun s => Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * f s)
      volume 0 t := by
  have he : Continuous (fun s : ℝ => Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s))) := by
    fun_prop
  exact (hf.mono_set (by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2)).continuousOn_mul he.continuousOn

theorem norm_integral_osc_le (f : ℝ → ℂ) (hf : IntervalIntegrable f volume 0 1)
    (z : ℂ) {t : ℝ} (ht : t ∈ Icc 0 1) :
    ‖∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * f s‖ ≤
      Real.exp (|z.im| * t) * ∫ s : ℝ in 0..1, ‖f s‖ := by
  have hi := intervalIntegrable_osc f hf z ht
  have hsub : uIcc (0 : ℝ) t ⊆ uIcc 0 1 := by
    rw [uIcc_of_le ht.1, uIcc_of_le zero_le_one]
    exact Icc_subset_Icc le_rfl ht.2
  have hn := hf.norm.mono_set hsub
  calc ‖∫ s : ℝ in 0..t, Complex.exp (Complex.I * z * ((t : ℂ) - 2 * s)) * f s‖
      ≤ ∫ s : ℝ in 0..t, Real.exp (|z.im| * t) * ‖f s‖ := by
        apply intervalIntegral.norm_integral_le_of_norm_le ht.1
        · exact Filter.Eventually.of_forall (fun s hs => by
            rw [norm_mul]
            exact mul_le_mul_of_nonneg_right
              (norm_osc_exp_le z ht.1 ⟨hs.1.le, hs.2⟩) (norm_nonneg _))
        · exact hn.const_mul _
    _ = Real.exp (|z.im| * t) * ∫ s : ℝ in 0..t, ‖f s‖ :=
        intervalIntegral.integral_const_mul _ _
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
        (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hf.norm

end

end NlsGge.GK38
