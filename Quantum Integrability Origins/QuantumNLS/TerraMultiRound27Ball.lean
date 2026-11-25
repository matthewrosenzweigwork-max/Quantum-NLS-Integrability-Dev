import QuantumNLS.TerraMultiRound27Compression

/-! An explicit common ball and the sign-flip covariance without compression assumptions. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory
namespace QuantumNLS.LocalSpectral.Round27
open QuantumNLS.Local002 Round26

variable {L κ r : ℝ}

def compressionRadius (κ L r : ℝ) : ℝ :=
  (2 * (1 + 2 * Real.sqrt κ * Cconst L r))⁻¹

theorem compressionRadius_pos (κ L r : ℝ) : 0 < compressionRadius κ L r := by
  unfold compressionRadius
  have h := Cconst_nonneg L r
  positivity

theorem qpar_lt_half_of_norm_lt_radius (u : Lp ℂ 2 (μI L))
    (hu : ‖u‖ < compressionRadius κ L r) : qpar κ L r u < 1 / 2 := by
  let c : ℝ := 2 * Real.sqrt κ * Cconst L r
  have hc : 0 ≤ c := by
    dsimp [c]
    have h := Cconst_nonneg L r
    positivity
  have hd : 0 < 2 * (1 + c) := by positivity
  have hnorm : ‖u‖ < (2 * (1 + c))⁻¹ := hu
  have hprod : c * ‖u‖ < c * (2 * (1 + c))⁻¹ + (2 * (1 + c))⁻¹ := by
    have ha : c * ‖u‖ ≤ c * (2 * (1 + c))⁻¹ := mul_le_mul_of_nonneg_left hnorm.le hc
    have hb : 0 < (2 * (1 + c))⁻¹ := inv_pos.mpr hd
    linarith
  have hsum : c * (2 * (1 + c))⁻¹ + (2 * (1 + c))⁻¹ = 1 / 2 := by
    field_simp
    ring
  change c * ‖u‖ < 1 / 2
  linarith

theorem smallCompression_on_ball (hL : 0 < L) (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (u : Lp ℂ 2 (μI L))
    (hu : ‖u‖ < compressionRadius κ L r) (n : ℤ) :
    SmallCompression L κ (u : ℝ → ℂ) n r ∧
      SmallCompression L κ (fun t => -(u : ℝ → ℂ) t) n r :=
  smallCompression_both hL hyp hr hr2 n u (qpar_lt_half_of_norm_lt_radius u hu)

/-- Sign covariance for the actual reduced maps, with both compression bounds
constructed from the single uniform ball condition. -/
theorem reducedMatrix_parity_on_ball (hL : 0 < L) (hyp : FreeResolventHyp L κ)
    (hr : 0 < r) (hr2 : r < 2 * Real.pi / L) (u : Lp ℂ 2 (μI L))
    (hu : ‖u‖ < compressionRadius κ L r) (n : ℤ) :
    let h := smallCompression_on_ball hL hyp hr hr2 u hu n
    SemiconjBy fiberParity (reducedMatrix2 L κ (u : ℝ → ℂ) n r h.1)
      (reducedMatrix2 L κ (fun t => -(u : ℝ → ℂ) t) n r h.2) := by
  dsimp only
  apply reducedMatrix_parity hyp hr hr2 n u
  have h := qpar_lt_half_of_norm_lt_radius u hu
  linarith

end QuantumNLS.LocalSpectral.Round27
#print axioms QuantumNLS.LocalSpectral.Round27.compressionRadius_pos
#print axioms QuantumNLS.LocalSpectral.Round27.qpar_lt_half_of_norm_lt_radius
#print axioms QuantumNLS.LocalSpectral.Round27.smallCompression_on_ball
#print axioms QuantumNLS.LocalSpectral.Round27.reducedMatrix_parity_on_ball
