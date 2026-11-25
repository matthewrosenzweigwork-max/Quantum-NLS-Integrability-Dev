import QuantumNLS.TerraMultiRound59SignedCharges

/-! The first retained coefficient is the quartic polynomial at order one. -/
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace QuantumNLS.TerraMultiRound64FirstRetained
open QuantumNLS.Sobolev QuantumNLS.TranslatedCorrelation
open QuantumNLS.TerraMultiRound49SobolevBridge QuantumNLS.TerraMultiRound59SobolevCoordinates
open QuantumNLS.TerraMultiRound59SignedCharges QuantumNLS.TerraMultiRound59RCompatibility
open QuantumNLS.TerraMultiRound59QuarticTransfer
variable {L : ℝ} [Fact (0 < L)]

theorem retained_one (s : ℕ) (hs : 2 ≤ s) (κ : ℝ)
    (x : QuantumNLS.RiccatiSobolevBanach.Ell2)
    (hst : ((1 : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ)) :
    retainedR (L := L) s hs κ (physicalToHk (L := L) (s-1) x) 1 =
      R1field (L := L) κ (H02.mono (L := L) (s := ((1 : ℕ) : ℝ)) (t := ((s-1 : ℕ) : ℝ)) hst (physicalToHk (L := L) (s-1) x)) := by
  have h1 := odd_coefficient_signed (L := L) s hs κ x 1 (by omega) (by omega)
  have h2 := R1field_transfer (L := L) s hs κ (physicalToHk (L := L) (s-1) x) hst
  rw [coordinates_physical] at h2
  norm_num only [Nat.reduceMul, Nat.reduceAdd, pow_one, neg_one_mul] at h1
  linarith

#print axioms retained_one
end QuantumNLS.TerraMultiRound64FirstRetained
