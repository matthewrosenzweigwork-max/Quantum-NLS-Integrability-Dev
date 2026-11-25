import QuantumNLS.TerraMultiRound39PhysicalBall

/-! Quantitative first nonlinear Picard approximation for REG-007.
This is a partial result, not the scalar-expansion theorem. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound44Picard
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound38SignedPicard QuantumNLS.TerraMultiRound39PhysicalBall

/-- A small physical fixed point differs from the free resolvent by at most
cubic order in the inverse spectral parameter. -/
theorem nonlinear_cubic_bound {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hL ha hY κ u r = r)
    (hn : ‖r‖ ≤ 2 * ‖u‖ / |Y|) :
    ‖r - signedCLM L Y hY u‖ ≤
      (4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3 := by
  have h := norm_signedT_sub_le hL ha hY (κ / L) ‖u‖ u (jEll u) r 0
    (by rw [norm_jEll])
  have hf : signedT hL ha hY (κ / L) u (jEll u) r =
      physicalT hL ha hY κ u r := rfl
  rw [hf, hr, signedT_zero] at h
  simp only [norm_zero, add_zero, sub_zero] at h
  have hn' : ‖r‖ ≤ (2 * ‖u‖) * |Y|⁻¹ := by simpa [div_eq_mul_inv] using hn
  have hp : 0 ≤ |κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖ := by positivity
  calc
    ‖r - signedCLM L Y hY u‖ ≤
        (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) * (‖r‖ * ‖r‖) := h
    _ ≤ (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
        (((2 * ‖u‖) * |Y|⁻¹) * ((2 * ‖u‖) * |Y|⁻¹)) := by
          gcongr
    _ = (4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3 := by ring

/-- The first nonlinear Picard iterate approximates the small solution to
fifth order. This is the first tail estimate in the tree expansion. -/
theorem first_picard_fifth_order {L a Y : ℝ} (hL : 0 < L) (ha : 1 / 2 < a)
    (hY : 0 < |Y|) (κ : ℝ) (u r : Ell2)
    (hr : physicalT hL ha hY κ u r = r)
    (hn : ‖r‖ ≤ 2 * ‖u‖ / |Y|) :
    ‖r - physicalT hL ha hY κ u (signedCLM L Y hY u)‖ ≤
      (12 * (|κ / L| * Cmul L a ^ 2) ^ 2 * ‖u‖ ^ 5) * |Y|⁻¹ ^ 5 := by
  have h := norm_signedT_sub_le hL ha hY (κ / L) ‖u‖ u (jEll u)
    r (signedCLM L Y hY u) (by rw [norm_jEll])
  change ‖physicalT hL ha hY κ u r -
      physicalT hL ha hY κ u (signedCLM L Y hY u)‖ ≤ _ at h
  rw [hr] at h
  have hn' : ‖r‖ ≤ (2 * ‖u‖) * |Y|⁻¹ := by simpa [div_eq_mul_inv] using hn
  have hf : ‖signedCLM L Y hY u‖ ≤ ‖u‖ * |Y|⁻¹ := by
    simpa [mul_comm] using norm_signedCLM_le L Y hY u
  have hd := nonlinear_cubic_bound hL ha hY κ u r hr hn
  have hC : 0 ≤ Cmul L a := Real.sqrt_nonneg _
  have hi : 0 ≤ |Y|⁻¹ := inv_nonneg.mpr hY.le
  have hcoeff : 0 ≤ |κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖ := by positivity
  have hsum : ‖r‖ + ‖signedCLM L Y hY u‖ ≤ 3 * ‖u‖ * |Y|⁻¹ := by
    nlinarith
  have hbound : 0 ≤ 4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3 * |Y|⁻¹ ^ 3 := by positivity
  calc
    ‖r - physicalT hL ha hY κ u (signedCLM L Y hY u)‖ ≤
        (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
          ((‖r‖ + ‖signedCLM L Y hY u‖) * ‖r - signedCLM L Y hY u‖) := h
    _ ≤ (|κ / L| * |Y|⁻¹ * Cmul L a ^ 2 * ‖u‖) *
          ((3 * ‖u‖ * |Y|⁻¹) *
            ((4 * |κ / L| * Cmul L a ^ 2 * ‖u‖ ^ 3) * |Y|⁻¹ ^ 3)) := by
          gcongr
    _ = (12 * (|κ / L| * Cmul L a ^ 2) ^ 2 * ‖u‖ ^ 5) * |Y|⁻¹ ^ 5 := by ring

#print axioms nonlinear_cubic_bound
#print axioms first_picard_fifth_order
end QuantumNLS.TerraMultiRound44Picard
