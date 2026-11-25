import QuantumNLS.Ext025A7Spectral

/-! Quantitative inverse disk for LOCAL-009. The source quarter-derivative
bound is the only analytic estimate supplied; existence, uniqueness, an
interior preimage and a nonzero derivative are consequences. -/
set_option autoImplicit false
noncomputable section
open Set Filter Topology Metric
open scoped NNReal
namespace QuantumNLS.Ext025A7

/-- Exact three-quarter lower bound on the full closed source disk. -/
theorem normalizedSpectral_lower (κ L : ℝ) {z : ℂ} {R : ℝ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    {w v : ℂ} (hw : w ∈ closedBall (0 : ℂ) R) (hv : v ∈ closedBall (0 : ℂ) R) :
    (3 / 4 : ℝ) * ‖w - v‖ ≤
      ‖normalizedSpectral κ L z w - normalizedSpectral κ L z v‖ := by
  have ha := normalizedSpectral_approximates κ L hD hb w hw v hv
  have ht : ‖w - v‖ ≤
      ‖normalizedSpectral κ L z w - normalizedSpectral κ L z v‖ +
      ‖normalizedSpectral κ L z w - normalizedSpectral κ L z v - (w - v)‖ := by
    calc
      ‖w - v‖ = ‖(normalizedSpectral κ L z w - normalizedSpectral κ L z v) -
        (normalizedSpectral κ L z w - normalizedSpectral κ L z v - (w - v))‖ := by
          congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  change ‖normalizedSpectral κ L z w - normalizedSpectral κ L z v - (w - v)‖ ≤
    ((1 / 4 : ℝ≥0) : ℝ) * ‖w - v‖ at ha
  norm_num at ha
  linarith

theorem normalizedSpectral_injOn (κ L : ℝ) {z : ℂ} {R : ℝ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4) :
    InjOn (normalizedSpectral κ L z) (closedBall (0 : ℂ) R) := by
  intro w hw v hv he
  have h := normalizedSpectral_lower κ L hD hb hw hv
  rw [he, sub_self, norm_zero] at h
  have : ‖w - v‖ = 0 := by nlinarith [norm_nonneg (w-v)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Construct a preimage by the quantitative Banach inverse theorem.
The strict target margin proves the preimage is in the open source disk. -/
theorem normalizedSpectral_disk (κ L : ℝ) {z t : ℂ} {R : ℝ}
    (hR : 0 < R) (hD : spectralLinear κ L z ≠ 0)
    (hb : ∀ w ∈ closedBall (0 : ℂ) R,
      ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
        ‖spectralLinear κ L z‖ / 4)
    (ht : ‖t‖ < 3 / 4 * R) :
    ∃ w ∈ ball (0 : ℂ) R, normalizedSpectral κ L z w = t ∧
      ∀ v ∈ closedBall (0 : ℂ) R, normalizedSpectral κ L z v = t → v = w := by
  have ha := normalizedSpectral_approximates κ L hD hb
  have hs := ha.surjOn_closedBall_of_nonlinearRightInverse
    (ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse hR.le (Subset.refl _)
  have hz : normalizedSpectral κ L z 0 = 0 := by simp [normalizedSpectral]
  have ht' : t ∈ closedBall (normalizedSpectral κ L z 0)
      ((((ContinuousLinearEquiv.refl ℂ ℂ).toNonlinearRightInverse.nnnorm : ℝ)⁻¹ -
        ((1 / 4 : ℝ≥0) : ℝ)) * R) := by
    norm_num [hz, mem_closedBall, dist_eq_norm, ContinuousLinearEquiv.toNonlinearRightInverse]
    exact ht.le
  obtain ⟨w, hw, he⟩ := hs ht'
  have hl := normalizedSpectral_lower κ L hD hb hw
    (show (0 : ℂ) ∈ closedBall (0 : ℂ) R by simp [hR.le])
  simp only [he, hz, sub_zero] at hl
  have hwi : w ∈ ball (0 : ℂ) R := by
    rw [mem_ball, dist_zero_right]
    nlinarith
  exact ⟨w, hwi, he, fun v hv hv' =>
    normalizedSpectral_injOn κ L hD hb hv hw (hv'.trans he.symm)⟩

/-- The derivative is separated from zero throughout the source disk. -/
theorem spectralDerivative_nonzero (κ L : ℝ) {z w : ℂ}
    (hD : spectralLinear κ L z ≠ 0)
    (hb : ‖spectralDerivative κ L z w - spectralLinear κ L z‖ ≤
      ‖spectralLinear κ L z‖ / 4) : spectralDerivative κ L z w ≠ 0 := by
  intro he
  rw [he, zero_sub, norm_neg] at hb
  have hp := norm_pos_iff.mpr hD
  linarith

end QuantumNLS.Ext025A7
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_lower
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_injOn
#print axioms QuantumNLS.Ext025A7.normalizedSpectral_disk
#print axioms QuantumNLS.Ext025A7.spectralDerivative_nonzero
