import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The actual DVD operator has zero true-to-true matrix coefficients because
the paired potential exchanges the two parity components. -/
theorem freeResolventPotentialFreeResolvent_true_true_entry_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, l))) = 0 := by
  rw [← parityPairRepr_inner, freeResolventPotentialFreeResolvent_repr_apply]
  rw [freeResolventParityPair_apply_basis]
  simp [parityPairRepr_apply, coveredH1ParityPairPotential_apply_true, parityPairVector,
    mixedIndex, PiLp.single_apply]

/-- The actual DVD operator has zero false-to-false matrix coefficients for
the same off-diagonal parity reason. -/
theorem freeResolventPotentialFreeResolvent_false_false_entry_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, l))) = 0 := by
  rw [← parityPairRepr_inner, freeResolventPotentialFreeResolvent_repr_apply]
  rw [freeResolventParityPair_apply_basis]
  simp [parityPairRepr_apply, coveredH1ParityPairPotential_apply_false, parityPairVector,
    mixedIndex, PiLp.single_apply]

end NlsGge.Schur
