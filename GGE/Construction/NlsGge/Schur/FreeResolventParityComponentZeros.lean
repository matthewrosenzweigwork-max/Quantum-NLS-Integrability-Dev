import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The DVP column with false resonant input has no false output component. -/
theorem freeResolventPotentialColumn_false_resonant_false_component_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    parityPairRepr n
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, resonantIndex n))) (false, m) = 0 := by
  rw [freeResolventPotentialColumn_repr_apply u₁ u₂ hu₁ hu₂ n z hz
    (parityPairVector n (false, resonantIndex n)) (false, m)]
  rw [parityPairRepr_apply]
  have hzero : coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (resonantParityPair n (parityPairVector n (false, resonantIndex n))) false = 0 := by
    rw [coveredH1ParityPairPotential_apply_false]
    have hr : resonantParityPair n (parityPairVector n
        (false, resonantIndex n)) = parityPairVector n
          (false, resonantIndex n) := by
      simpa using resonantParityPair_apply_basis n
        (false, resonantIndex n)
    rw [hr]
    simp [parityPairVector]
  rw [hzero]
  simp

/-- The DVP column with true resonant input has no true output component. -/
theorem freeResolventPotentialColumn_true_resonant_true_component_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    parityPairRepr n
      (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, resonantIndex n))) (true, m) = 0 := by
  rw [freeResolventPotentialColumn_repr_apply u₁ u₂ hu₁ hu₂ n z hz
    (parityPairVector n (true, resonantIndex n)) (true, m)]
  rw [parityPairRepr_apply]
  have hzero : coveredH1ParityPairPotential u₁ u₂ hu₁ hu₂ n
      (resonantParityPair n (parityPairVector n (true, resonantIndex n))) true = 0 := by
    rw [coveredH1ParityPairPotential_apply_true]
    have hr : resonantParityPair n (parityPairVector n
        (true, resonantIndex n)) = parityPairVector n
          (true, resonantIndex n) := by
      simpa using resonantParityPair_apply_basis n
        (true, resonantIndex n)
    rw [hr]
    simp [parityPairVector]
  rw [hzero]
  simp

/-- The actual PVD row has zero same-parity true matrix entries. -/
theorem resonantPotentialFreeResolventRow_true_true_entry_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (true, m))
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, l))) = 0 := by
  rw [← parityPairRepr_inner, resonantPotentialFreeResolventRow_repr_apply
    u₁ u₂ hu₁ hu₂ n z hz (parityPairVector n (true, l)) (true, m)]
  by_cases hm : m = resonantIndex n
  · rw [if_pos hm, freeResolventParityPair_apply_basis, parityPairRepr_apply]
    rw [coveredH1ParityPairPotential_apply_true]
    simp [parityPairVector]
  · simp [hm]

/-- The actual PVD row has zero same-parity false matrix entries. -/
theorem resonantPotentialFreeResolventRow_false_false_entry_zero
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m l : Sector n) :
    inner ℂ (parityPairVector n (false, m))
      (resonantPotentialFreeResolventRow u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, l))) = 0 := by
  rw [← parityPairRepr_inner, resonantPotentialFreeResolventRow_repr_apply
    u₁ u₂ hu₁ hu₂ n z hz (parityPairVector n (false, l)) (false, m)]
  by_cases hm : m = resonantIndex n
  · rw [if_pos hm, freeResolventParityPair_apply_basis, parityPairRepr_apply]
    rw [coveredH1ParityPairPotential_apply_false]
    simp [parityPairVector]
  · simp [hm]

end NlsGge.Schur
