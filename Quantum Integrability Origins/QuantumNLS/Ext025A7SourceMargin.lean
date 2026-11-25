import QuantumNLS.Ext025A7Uniform
import Mathlib.Analysis.Real.Pi.Bounds

/-! Derive LOCAL-009's quarter-derivative estimate from the source's
explicit exponential/gap/small-radius bounds, then bind the entire GP-03
scalar inverse application. These scalar source margins do not assume any
inverse, root, derivative of an inverse, or Banach analytic conclusion. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
namespace QuantumNLS.Ext025A7

/-- The report's literal R=2M/d, d=pi/(4L), satisfies the margin
used by the wrapper from its stated kappa*L*M bound. -/
theorem local009_report_radius {κ L M : ℝ}
    (hL : 0 < L) (hM : 0 < M) (hsmall : κ * L * M ≤ 1 / 1000000) :
    0 < 8 * M * L / Real.pi ∧ κ * (8 * M * L / Real.pi) ≤ 1 / 1000 := by
  constructor
  · positivity
  · calc
      κ * (8 * M * L / Real.pi) = 8 * (κ * L * M) / Real.pi := by ring
      _ ≤ 8 * (1 / 1000000) / Real.pi := by gcongr
      _ ≤ 1 / 1000 := (div_le_iff₀ Real.pi_pos).2 (by nlinarith [Real.pi_gt_three])

/-- The source has kappa R < 3e-6, so this weaker 1/1000 margin suffices.
The exponential estimate is proved on the full closed source disk. -/
theorem local009_quarter_from_source {κ L R : ℝ} {z w : ℂ}
    (hκ : 0 < κ) (hsmall : κ * R ≤ 1 / 1000)
    (hexp : ‖Complex.exp (Complex.I * z * L)‖ ≤ 8)
    (hgap : 1 / 2 ≤ ‖1 - Complex.exp (Complex.I * z * L)‖)
    (hw : w ∈ closedBall (0 : ℂ) R) :
    ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      ‖spectralLinear κ L z‖ / 4 := by
  have hwr : ‖w‖ ≤ R := by simpa [mem_closedBall, dist_zero_right] using hw
  have hkw : κ * ‖w‖ ≤ 1 / 1000 :=
    (mul_le_mul_of_nonneg_left hwr hκ.le).trans hsmall
  have hna : ‖Complex.I * κ * w‖ = κ * ‖w‖ := by
    simp [abs_of_pos hκ]
  have hnb : ‖-Complex.I * κ * w‖ = κ * ‖w‖ := by
    simp [abs_of_pos hκ]
  have hpa := Complex.norm_exp_sub_one_le (x := Complex.I * κ * w) (by rw [hna]; linarith)
  have hpb := Complex.norm_exp_sub_one_le (x := -Complex.I * κ * w) (by rw [hnb]; linarith)
  rw [hna] at hpa
  rw [hnb] at hpb
  have heq : spectralDerivative κ L z w - spectralLinear κ L z =
      (Complex.I * κ) * (Complex.exp (Complex.I * κ * w) - 1) +
      Complex.exp (Complex.I * z * L) * (-Complex.I * κ) *
        (Complex.exp (-Complex.I * κ * w) - 1) := by
    unfold spectralDerivative spectralLinear
    ring
  have hnorm : ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      κ * ‖Complex.exp (Complex.I * κ * w) - 1‖ +
      ‖Complex.exp (Complex.I * z * L)‖ * κ *
        ‖Complex.exp (-Complex.I * κ * w) - 1‖ := by
    rw [heq]
    simpa [norm_mul, abs_of_pos hκ] using norm_add_le
      ((Complex.I * κ) * (Complex.exp (Complex.I * κ * w) - 1))
      (Complex.exp (Complex.I * z * L) * (-Complex.I * κ) *
        (Complex.exp (-Complex.I * κ * w) - 1))
  have hbound : ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      κ * (2 * (κ * ‖w‖)) + 8 * κ * (2 * (κ * ‖w‖)) := by
    apply hnorm.trans
    gcongr
  have hlo : κ / 2 ≤ ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm, abs_of_pos hκ]
    nlinarith
  have hmul := mul_le_mul_of_nonneg_left hkw hκ.le
  nlinarith

/-- Precise application binding: exact 3|D|R/4 target disk, unique inverse
with values in |w|<R, joint complex analyticity, both derivative formulas and
uniform first/second derivative bounds depending only on kappa. -/
theorem local009_application (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hsmall : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (Complex.I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (Complex.I * z * L)‖)
    {z y : ℂ} (hz : z ∈ U)
    (hy : ‖y - spectralMap κ L z 0‖ < 3 / 4 * ‖spectralLinear κ L z‖ * R) :
    spectralInverse κ L R z y ∈ ball (0 : ℂ) R ∧
      spectralMap κ L z (spectralInverse κ L R z y) = y ∧
      (∀ v ∈ closedBall (0 : ℂ) R, spectralMap κ L z v = y →
        v = spectralInverse κ L R z y) ∧
      AnalyticAt ℂ (fun p : ℂ × ℂ => spectralInverse κ L R p.1 p.2) (z, y) ∧
      HasDerivAt (spectralInverse κ L R z)
        (spectralDerivative κ L z (spectralInverse κ L R z y))⁻¹ y ∧
      HasDerivAt (deriv (spectralInverse κ L R z))
        ((κ : ℂ)^2 * y / (spectralDerivative κ L z (spectralInverse κ L R z y))^3) y ∧
      ‖deriv (spectralInverse κ L R z) y‖ ≤ (3 * κ / 8)⁻¹ ∧
      ‖deriv (deriv (spectralInverse κ L R z)) y‖ ≤ κ^2 * 16 / (3 * κ / 8)^3 := by
  have hD : ∀ z ∈ U, spectralLinear κ L z ≠ 0 := by
    intro v hv
    rw [← norm_pos_iff, spectralLinear_norm, abs_of_pos hκ]
    exact mul_pos hκ ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hgap v hv))
  have hb : ∀ v ∈ U, ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L v w - spectralLinear κ L v‖ ≤
        ‖spectralLinear κ L v‖ / 4 :=
    fun v hv w hw => local009_quarter_from_source hκ hsmall (hexp v hv) (hgap v hv) hw
  obtain ⟨hw, he, hu, han⟩ := local009_spectral_inverse κ L hR hU hD hb hz hy
  obtain ⟨hb1, hb2⟩ := local009_uniform_inverse_bounds κ L hκ hR
    (by linarith : κ * R ≤ 1) hU hexp hgap hb hz hy
  exact ⟨hw, he, hu, han, local009_inverse_hasDerivAt κ L hR hU hD hb hz hy,
    local009_inverse_second κ L hR hU hD hb hz hy, hb1, hb2⟩
/-- The uniformly selected inverse has the source's exact central value. -/
theorem local009_inverse_center (κ L : ℝ) {R : ℝ} {U : Set ℂ}
    (hκ : 0 < κ) (hR : 0 < R) (hsmall : κ * R ≤ 1 / 1000) (hU : IsOpen U)
    (hexp : ∀ z ∈ U, ‖Complex.exp (Complex.I * z * L)‖ ≤ 8)
    (hgap : ∀ z ∈ U, 1 / 2 ≤ ‖1 - Complex.exp (Complex.I * z * L)‖)
    {z : ℂ} (hz : z ∈ U) : spectralInverse κ L R z (spectralMap κ L z 0) = 0 := by
  have hp : 0 < ‖spectralLinear κ L z‖ := by
    rw [spectralLinear_norm, abs_of_pos hκ]
    exact mul_pos hκ ((by norm_num : (0 : ℝ) < 1 / 2).trans_le (hgap z hz))
  have hy : ‖spectralMap κ L z 0 - spectralMap κ L z 0‖ <
      3 / 4 * ‖spectralLinear κ L z‖ * R := by simp only [sub_self, norm_zero]; positivity
  have hu := (local009_application κ L hκ hR hsmall hU hexp hgap hz hy).2.2.1
  exact (hu 0 (by simp [hR.le]) rfl).symm

end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.local009_quarter_from_source
#print axioms QuantumNLS.Ext025A7.local009_application

#print axioms QuantumNLS.Ext025A7.local009_report_radius
#print axioms QuantumNLS.Ext025A7.local009_inverse_center
