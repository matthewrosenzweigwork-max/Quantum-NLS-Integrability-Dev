import NlsGge.GK38.EigenvalueCompactnessDefs

/-! # S7: metric estimates for normalized complex curves

These estimates use a lower bound for the one limiting curve only.
-/
set_option autoImplicit false
open Filter Topology Set Metric
open NlsGge.Pilot
namespace NlsGge.GK38
noncomputable section

theorem complex_normalization_distance38 (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    ‖z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ)‖ ≤ 2 * ‖z - w‖ / ‖w‖ := by
  have hz' : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hz)
  have hw' : (‖w‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hw)
  have hu : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
    exact div_self (norm_ne_zero_iff.mpr hz)
  have he : z / (‖z‖ : ℂ) - w / (‖w‖ : ℂ) =
      (z - w) / (‖w‖ : ℂ) + (z / (‖z‖ : ℂ)) * ((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖w‖ : ℂ) := by
    push_cast
    field_simp
    ring
  rw [he]
  calc
    _ ≤ ‖(z - w) / (‖w‖ : ℂ)‖ +
        ‖(z / (‖z‖ : ℂ)) * ((‖w‖ - ‖z‖ : ℝ) : ℂ) / (‖w‖ : ℂ)‖ := norm_add_le _ _
    _ = ‖z - w‖ / ‖w‖ + |‖w‖ - ‖z‖| / ‖w‖ := by
      simp only [norm_div, norm_mul, hu, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (norm_nonneg w), one_mul]
    _ ≤ ‖z - w‖ / ‖w‖ + ‖z - w‖ / ‖w‖ := by
      exact add_le_add le_rfl (div_le_div_of_nonneg_right
        (by simpa only [abs_sub_comm] using abs_norm_sub_norm_le z w) (norm_nonneg w))
    _ = _ := by ring

theorem phase_exponential_distance38 (θ ψ : ℝ) :
    ‖Complex.exp (-Complex.I * (θ : ℂ)) - Complex.exp (-Complex.I * (ψ : ℂ))‖ =
      ‖Complex.exp (-Complex.I * ((θ - ψ : ℝ) : ℂ)) - 1‖ := by
  have he : -Complex.I * (θ : ℂ) = -Complex.I * (ψ : ℂ) +
      -Complex.I * ((θ - ψ : ℝ) : ℂ) := by push_cast; ring
  have hn : ‖Complex.exp (-Complex.I * (ψ : ℂ))‖ = 1 := by
    simp [Complex.norm_exp, Complex.mul_re]
  rw [he, Complex.exp_add]
  have hf : Complex.exp (-Complex.I * (ψ : ℂ)) * Complex.exp (-Complex.I * ((θ - ψ : ℝ) : ℂ)) -
      Complex.exp (-Complex.I * (ψ : ℂ)) =
      Complex.exp (-Complex.I * (ψ : ℂ)) * (Complex.exp (-Complex.I * ((θ - ψ : ℝ) : ℂ)) - 1) := by ring
  rw [hf, norm_mul, hn, one_mul]

theorem phase_chord_positive38 (η : ℝ) (hη : 0 < η) (hπ : η < Real.pi) :
    0 < ‖Complex.exp (-Complex.I * (η : ℂ)) - 1‖ ∧
    0 < ‖Complex.exp (-Complex.I * ((-η : ℝ) : ℂ)) - 1‖ := by
  have hs := Real.sin_pos_of_pos_of_lt_pi hη hπ
  have hp : (Complex.exp (-Complex.I * (η : ℂ))).im = -Real.sin η := by
    rw [show -Complex.I * (η : ℂ) = (-η : ℂ) * Complex.I by ring, Complex.exp_mul_I]
    simp [Complex.mul_im, ← Complex.ofReal_sin]
  have hn : (Complex.exp (-Complex.I * ((-η : ℝ) : ℂ))).im = Real.sin η := by
    rw [show -Complex.I * ((-η : ℝ) : ℂ) = (η : ℂ) * Complex.I by push_cast; ring, Complex.exp_mul_I]
    simp [Complex.mul_im, ← Complex.ofReal_sin]
  constructor
  · apply norm_pos_iff.mpr
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    rw [hp, Complex.one_im] at hi
    linarith
  · apply norm_pos_iff.mpr
    intro he
    have hi := congrArg Complex.im (sub_eq_zero.mp he)
    rw [hn, Complex.one_im] at hi
    linarith

end
end NlsGge.GK38
