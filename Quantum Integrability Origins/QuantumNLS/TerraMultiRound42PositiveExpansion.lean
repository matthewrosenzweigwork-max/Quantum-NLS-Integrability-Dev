import QuantumNLS.TerraMultiRound39PhysicalBall
import QuantumNLS.RiccatiExpansions

/-! Positive-height all-order remainder in the existing high-order Fourier
model. Physical signed coefficient identification and negative heights remain. -/
set_option autoImplicit false
noncomputable section
open Complex
namespace QuantumNLS.TerraMultiRound42PositiveExpansion
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1
open QuantumNLS.RiccatiSobolevE2 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.RiccatiChargeLevels QuantumNLS.RiccatiRemainder
open QuantumNLS.RiccatiExpansions QuantumNLS.ComplexifiedSobolevField
open QuantumNLS.TerraMultiRound39PhysicalBall

/-- For every truncation order, the positive signed solution has the native
Fourier-model remainder bound, at the explicit large-height threshold. -/
theorem positive_model_expansion {L a S Y : ℝ} {M : ℕ}
    (hL : 0 < L) (ha : 1 / 2 < a) (haS : a + (M : ℝ) + 1 ≤ S)
    (hM : 1 ≤ M) (κ : ℝ) (u : Ell2) (β : ℝ) (hβ : 0 < β)
    (hu : ‖u‖ ≤ β)
    (D : Ell2 →ₗ[ℂ] Ell2) (hD : ∀ y : dDom L, D (y : Ell2) = dmulEll L y)
    (hY : 0 < Y) (hR : remR L a S M (κ / L) β 1 ≤ Y)
    (r : Ell2)
    (hr : physicalT hL ha (abs_pos.mpr hY.ne') κ (lowT L a S u) r = r)
    (hrn : ‖r‖ ≤ 2 * β / Y) :
    ‖r - rMsum (wAbs (mulLin hL ha) D (jEll (lowT L a S u))
        (lowT L a S u) ((κ / L : ℝ) : ℂ)) (((Y : ℂ) * Complex.I)⁻¹) M‖
      ≤ remC L a S M (κ / L) β 1 * (Y ^ (M + 1))⁻¹ := by
  have hz : 0 < (((Y : ℂ) * Complex.I).im) := by simpa using hY
  have hnorm : ‖(Y : ℂ) * Complex.I‖ = Y := by
    simp [abs_of_pos hY]
  have hsec : (1 : ℝ) * ‖(Y : ℂ) * Complex.I‖ ≤ (((Y : ℂ) * Complex.I).im) := by
    simp [abs_of_pos hY]
  have hfix := hr
  rw [physicalT_positive hL ha hY] at hfix
  have hfix' : QuantumNLS.RiccatiPicardBall.riccatiT hL ha hz (κ / L)
      (lowT L a S u) (lowT L a S (jEll u)) r = r := by
    rw [lowT_jEll]
    exact hfix
  have hb := (expansion_a L hL ha haS hM (κ / L) u (jEll u) β hβ hu
    (by rw [norm_jEll]; exact hu) D hD 1 (by norm_num)
    ((Y : ℂ) * Complex.I) hz hsec (by simpa [abs_of_pos hY] using hR)).2 r hfix'
      (by simpa using hrn)
  simpa [lowT_jEll, abs_of_pos hY] using hb

#print axioms positive_model_expansion
end QuantumNLS.TerraMultiRound42PositiveExpansion
