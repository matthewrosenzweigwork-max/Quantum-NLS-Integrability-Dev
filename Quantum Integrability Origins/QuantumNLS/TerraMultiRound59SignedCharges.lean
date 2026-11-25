import QuantumNLS.TerraMultiRound59QuarticTransfer
import QuantumNLS.TerraMultiRound59RealExpansion

/-! Assemble the minimal-order polynomials on a common Sobolev domain. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59SignedCharges
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound57CollectedPowers
open QuantumNLS.TerraMultiRound59SobolevCoordinates QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound59Transfer QuantumNLS.TerraMultiRound59QuarticTransfer

variable {L : ℝ} [Fact (0 < L)]

def retainedR (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (u : Hk L (s - 1)) (j : ℕ) : ℝ :=
  if j = 1 then R1field (L := L) κ (H02.mono (L := L)
    (show ((1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ s - 1 by omega)) u)
  else if hj : 2 ≤ j ∧ j ≤ s then Rfield (L := L) j hj.1 κ (H02.mono (L := L)
    (show ((j - 1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) by exact_mod_cast (show j - 1 ≤ s - 1 by omega)) u)
  else 0

theorem odd_coefficient_signed (s : ℕ) (hs : 2 ≤ s) (κ : ℝ) (x : Ell2)
    (j : ℕ) (hj : 1 ≤ j) (hjs : j ≤ s) :
    (treeCoefficient (L := L) (k := s - 1) κ x s (2 * j + 1)).re =
      (-1 : ℝ) ^ j * retainedR (L := L) s hs κ (physicalToHk (L := L) (s - 1) x) j := by
  by_cases h1 : j = 1
  · subst j
    simp only [retainedR, ↓reduceDIte, ↓reduceIte, pow_one, neg_one_mul]
    have h := R1field_transfer (L := L) s hs κ (physicalToHk (L := L) (s - 1) x)
      (show ((1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ s - 1 by omega))
    rw [coordinates_physical] at h
    linarith
  · have hj2 : 2 ≤ j := by omega
    have h := Rfield_transfer (L := L) j s hj2 hjs κ (physicalToHk (L := L) (s - 1) x)
      (show ((j - 1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) by exact_mod_cast (show j - 1 ≤ s - 1 by omega))
    rw [coordinates_physical] at h
    simp only [retainedR, h1, ↓reduceIte, hj2, hjs, and_self, ↓reduceDIte]
    rw [h, ← mul_assoc]
    have hsign : (-1 : ℝ) ^ j * (-1 : ℝ) ^ j = 1 := by rw [← mul_pow]; norm_num
    rw [hsign, one_mul]

#print axioms retainedR
#print axioms odd_coefficient_signed
end QuantumNLS.TerraMultiRound59SignedCharges
