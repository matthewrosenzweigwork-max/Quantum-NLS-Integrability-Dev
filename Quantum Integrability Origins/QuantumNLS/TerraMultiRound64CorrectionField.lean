import QuantumNLS.TerraMultiRound59REG007

/-! The retained top coefficient is the minimal-domain correction polynomial. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace QuantumNLS.TerraMultiRound64CorrectionField
open QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation QuantumNLS.RiccatiSobolevBanach
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.TerraMultiRound59RCompatibility QuantumNLS.TerraMultiRound59Transfer
variable {L : ℝ} [Fact (0 < L)]

theorem retained_top (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (x : Ell2) :
    retainedR (L := L) s hs κ (physicalToHk (L := L) (s-1) x) s =
      Rfield (L := L) s hs κ (physicalToHk (L := L) (s-1) x) := by
  let w := physicalToHk (L := L) (s-1) x
  let hst : ((s-1 : ℕ) : ℝ) ≤ ((s-1 : ℕ) : ℝ) := le_rfl
  have hw : H02.mono (L := L) hst w = w := by
    apply WField.ext
    exact fieldIncl_val _ _ _ _ _
  have htr := Rfield_transfer (L := L) s s hs le_rfl κ w hst
  rw [hw] at htr
  dsimp only [w] at htr
  rw [coordinates_physical] at htr
  have hodd := odd_coefficient_signed (L := L) s hs κ x s (by omega) le_rfl
  rw [hodd] at htr
  have hsign : (-1 : ℝ)^s * (-1 : ℝ)^s = 1 := by rw [← mul_pow]; norm_num
  rw [← mul_assoc, hsign, one_mul] at htr
  exact htr.symm

#print axioms retained_top
end QuantumNLS.TerraMultiRound64CorrectionField
