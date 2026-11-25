import Mathlib

/-! The value estimate for a positive measure, before physical binding. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 400000
open Set MeasureTheory
namespace QuantumNLS.Q07TailValuesR24

theorem tail_value (μ : Measure ℝ) (r : ℕ) {a K : ℝ} (ha : 0 < a)
    (hr : Integrable (fun t : ℝ => |t|^r) μ)
    (hq : Integrable (fun t : ℝ => |t|^(2*r+2)) μ)
    (hK : ∫ t : ℝ, t^(2*r+2) ∂μ ≤ K) :
    |(∫ t : ℝ, t^r ∂μ) - ∫ t in Ioo (-a) a, t^r ∂μ| ≤ K / a^(r+2) := by
  have hi : Integrable (fun t : ℝ => t^r) μ := hr.mono'
    (by fun_prop) (ae_of_all _ fun t => by simp [Real.norm_eq_abs])
  have hp : ∀ t : ℝ, |t|^(2*r+2) = t^(2*r+2) := by
    intro t
    rw [show 2*r+2 = 2*(r+1) by omega,pow_mul, sq_abs,pow_mul]
  have ha' : 0 < a^(r+2) := pow_pos ha _
  have hd : (∫ t : ℝ, t^r ∂μ) - ∫ t in Ioo (-a) a, t^r ∂μ =
      ∫ t in (Ioo (-a) a)ᶜ, t^r ∂μ := by
    have he := integral_add_compl (s := Ioo (-a) a) measurableSet_Ioo hi
    linarith
  rw [hd,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ t in (Ioo (-a) a)ᶜ, |t|^r ∂μ := by
      simpa only [Real.norm_eq_abs,abs_pow] using norm_integral_le_integral_norm
        (f := fun t : ℝ => t^r) (μ := μ.restrict (Ioo (-a) a)ᶜ)
    _ ≤ ∫ t in (Ioo (-a) a)ᶜ, |t|^(2*r+2) / a^(r+2) ∂μ := by
      apply integral_mono_ae hr.integrableOn (hq.div_const _).integrableOn
      filter_upwards [ae_restrict_mem measurableSet_Ioo.compl] with t ht
      have hat : a ≤ |t| := by
        simp only [mem_compl_iff,mem_Ioo,not_and_or,not_lt] at ht
        rcases ht with ht | ht
        · exact le_trans (by linarith) (neg_le_abs t)
        · exact ht.trans (le_abs_self t)
      apply (le_div_iff₀ ha').mpr
      calc |t|^r*a^(r+2) ≤ |t|^r*|t|^(r+2) :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ ha.le hat _) (pow_nonneg (abs_nonneg _) _)
        _ = |t|^(2*r+2) := by rw [← pow_add]; congr 1; omega
    _ ≤ ∫ t : ℝ, |t|^(2*r+2) / a^(r+2) ∂μ :=
      integral_mono_measure Measure.restrict_le_self (ae_of_all _ fun t => by positivity)
        (hq.div_const _)
    _ = (∫ t : ℝ, t^(2*r+2) ∂μ) / a^(r+2) := by rw [integral_div]; simp_rw [hp]
    _ ≤ K / a^(r+2) := div_le_div_of_nonneg_right hK ha'.le
end QuantumNLS.Q07TailValuesR24
