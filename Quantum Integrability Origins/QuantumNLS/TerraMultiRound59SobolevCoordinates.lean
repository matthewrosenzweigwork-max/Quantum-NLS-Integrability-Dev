import QuantumNLS.TerraMultiRound59PhysicalLinear

/-! Equivalence of the physical Fourier coordinates with the realized Sobolev space. -/
set_option autoImplicit false
noncomputable section
namespace QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TranslatedCorrelation QuantumNLS.Sobolev
open QuantumNLS.RiccatiSobolevBanach QuantumNLS.RiccatiSobolevE1 QuantumNLS.RiccatiSobolevE2b
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59PhysicalLinear

variable {L : ℝ} [Fact (0 < L)]

def coordinates (k : ℕ) : Hk L k ≃ₗᵢ[ℂ] Ell2 :=
  (fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k))).trans
    (PosWeight.toL2ᵢ (def002 L k))

theorem coordinates_physical (k : ℕ) (x : Ell2) :
    coordinates (L := L) k (physicalToHk k x) = x := by
  ext n
  change (Real.sqrt ((def002 L k).w n) : ℂ) *
    (fourierHs (L := L) (one_le_def002 L (Nat.cast_nonneg k)) (physicalToHk k x)).val n = x n
  rw [fourierHs_val, physicalToHk_coeff]
  change (Real.sqrt (wt L (k : ℝ) n) : ℂ) * toField L (k : ℝ) x n = x n
  rw [wt_eq_pw_sq, Real.sqrt_sq (pw_pos L (k : ℝ) n).le]
  unfold toField
  exact mul_div_cancel₀ _ (pw_ne_zero L (k : ℝ) n)

theorem physical_coordinates (k : ℕ) (u : Hk L k) :
    physicalToHk k (coordinates (L := L) k u) = u := by
  apply (coordinates (L := L) k).injective
  rw [coordinates_physical]

#print axioms coordinates
#print axioms coordinates_physical
#print axioms physical_coordinates
end QuantumNLS.TerraMultiRound59SobolevCoordinates
