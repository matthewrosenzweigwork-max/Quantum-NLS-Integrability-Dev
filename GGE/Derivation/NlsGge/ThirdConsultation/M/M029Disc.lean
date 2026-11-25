import Mathlib
import NlsGge.ThirdConsultation.M.M029Host
import NlsGge.ThirdConsultation.M.M022Host

/-!
# M-029 support: `local_spectral_disc_in_strip` (proof development, AUTHOR; not self-reviewed)

Head: Pro round 14 (M-029 section) printed verbatim.  Route: `8 Q^2 <= <n>` gives `Q^2/<n> <= 1/8` and
`sqrt 2 * Q / <2n> <= 1/2`, so the radius is at most `5/8 <= pi/5`; the strip condition is `|Re| <= pi/2`.
-/

set_option autoImplicit false

noncomputable section

namespace NlsGge.ThirdConsultation.M

open NlsGge.GK38

theorem disc_radius_lt (Q : ℝ) (hQ : 0 ≤ Q) (n : ℤ)
    (hth : 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
      Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) < Real.pi / 5 := by
  have hρ : 1 ≤ NlsGge.Atomic.M.M054.indexWeight n := by
    unfold NlsGge.Atomic.M.M054.indexWeight; have := abs_nonneg (n : ℝ); linarith
  have hρ2 : NlsGge.Atomic.M.M054.indexWeight n ≤ NlsGge.Atomic.M.M054.indexWeight (2 * n) := by
    unfold NlsGge.Atomic.M.M054.indexWeight
    push_cast
    rw [abs_mul]
    have := abs_nonneg (n : ℝ)
    norm_num
    linarith
  set ρ := NlsGge.Atomic.M.M054.indexWeight n with hρdef
  set ρ2 := NlsGge.Atomic.M.M054.indexWeight (2 * n) with hρ2def
  have hρ2pos : 0 < ρ2 := by linarith
  have h1 : Q ^ 2 / ρ ≤ 1 / 8 := by
    rw [div_le_iff₀ (by linarith)]; linarith
  have h2 : Real.sqrt 2 * Q / ρ2 ≤ 1 / 2 := by
    rw [div_le_iff₀ hρ2pos]
    have hs : (Real.sqrt 2 * Q) ^ 2 ≤ (ρ2 / 2) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by norm_num)]
      nlinarith
    have := abs_le_of_sq_le_sq' hs (by linarith)
    nlinarith [this.2]
  have hpi : (3.14 : ℝ) < Real.pi := Real.pi_gt_d2
  linarith

theorem disc_radius_le (Q : ℝ) (hQ : 0 ≤ Q) (n : ℤ)
    (hth : 8 * Q ^ 2 ≤ NlsGge.Atomic.M.M054.indexWeight n) :
    Q ^ 2 / NlsGge.Atomic.M.M054.indexWeight n +
      Real.sqrt 2 * Q / NlsGge.Atomic.M.M054.indexWeight (2 * n) ≤ Real.pi / 5 :=
  (disc_radius_lt Q hQ n hth).le

theorem local_spectral_disc_in_strip
    (w : ℤ → ℝ) (hw : OneDerivativeWeight w) (φ : PotPair)
    (hφ : MTwoMode.potentialCoefficientEnergy w φ ≠ ⊤)
    (n : ℤ)
    (hthreshold : 8 * MTwoMode.potentialCoefficientNorm w φ ^ 2 ≤
      NlsGge.Atomic.M.M054.indexWeight n) :
    MTwoMode.localSpectralDisc w φ n ⊆
      Metric.closedBall ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 5) ∧
    Metric.closedBall ((n : ℂ) * (Real.pi : ℂ)) (Real.pi / 5) ⊆
      NlsGge.Atomic.KST004.spectralStrip n := by
  constructor
  · exact Metric.closedBall_subset_closedBall
      (disc_radius_le _ (Real.sqrt_nonneg _) n hthreshold)
  · intro z hz
    rw [Metric.mem_closedBall, dist_eq_norm] at hz
    unfold NlsGge.Atomic.KST004.spectralStrip
    have h1 : |z.re - (n : ℝ) * Real.pi| ≤ ‖z - (n : ℂ) * (Real.pi : ℂ)‖ := by
      have := Complex.abs_re_le_norm (z - (n : ℂ) * (Real.pi : ℂ))
      simpa using this
    show |z.re - (n : ℝ) * Real.pi| ≤ Real.pi / 2
    have hpi : 0 < Real.pi := Real.pi_pos
    linarith

end NlsGge.ThirdConsultation.M

end
