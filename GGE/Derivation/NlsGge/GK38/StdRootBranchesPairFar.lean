import NlsGge.GK38.StdRootBranchesPairScalar

/-! Far-index inverse-square correction, independent of spectral imaginary height. -/
set_option autoImplicit false
open Set Metric
namespace NlsGge.GK38
noncomputable section

theorem root_piN_norm38 (n : ℤ) (hn : n ≠ 0) :
    ‖(Lib.piN n : ℂ)‖ = |(n : ℝ)| * Real.pi := by
  rw [Lib.piN_of_ne hn, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_pos Real.pi_pos]

theorem rootFactor_split38 (n : ℤ) (p : PotPair × ℂ) :
    rootFactor38 n p = ((tauN p.1 n - p.2) / (Lib.piN n : ℂ)) *
      Complex.sqrt (1 - (gamma2 p.1 n / 4) / (tauN p.1 n - p.2)^2) := by
  unfold rootFactor38 stdRoot38
  ring

theorem root_far_sqrt_error38 {w g : ℂ} {G T : ℝ}
    (hg : ‖g‖ ≤ G) (hT : 0 < T) (hw : T / 2 ≤ ‖w‖) :
    ‖Complex.sqrt (1 - (g / 4) / w^2) - 1‖ ≤ G / T^2 := by
  have hwpos : 0 < ‖w‖ := by linarith
  calc
    _ ≤ ‖(g / 4) / w^2‖ := Lib.norm_sqrt_one_sub_sub_one_le _
    _ = ‖g‖ / (4 * ‖w‖^2) := by
      rw [norm_div, norm_div, norm_pow, Complex.norm_ofNat, div_div]
    _ ≤ G / T^2 := by
      apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
      have hG : 0 ≤ G := (norm_nonneg _).trans hg
      have hs : T^2 ≤ 4 * ‖w‖^2 := by nlinarith [norm_nonneg w]
      nlinarith [mul_le_mul_of_nonneg_left hs hG]

theorem root_pair_correction_decay38 {G t : ℝ} (_hG : 0 ≤ G) (ht : 1 ≤ t) :
    2 * (G / (t^2 * Real.pi^2)) + (G / (t^2 * Real.pi^2))^2 ≤
      (2 * G / Real.pi^2 + G^2 / Real.pi^4) / t^2 := by
  have htpos : 0 < t := by linarith
  have ht2 : 1 ≤ t^2 := by nlinarith
  have hden : 0 < t^4 * Real.pi^4 := by positivity
  apply (le_of_mul_le_mul_right ?_ hden)
  field_simp
  nlinarith [sq_nonneg G, mul_nonneg (sq_nonneg G) (show 0 ≤ t^2 - 1 by linarith)]

end
end NlsGge.GK38
