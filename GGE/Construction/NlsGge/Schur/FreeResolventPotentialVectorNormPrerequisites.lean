import NlsGge.Schur.FreeResolventPotentialOffDiagonalEntries

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot

/-- The exact ℓ² norm identity for the actual paired Fourier representation.
This is the typed normalization prerequisite for both resonant vector norms. -/
theorem parityPair_norm_sq_eq_tsum_repr_prerequisite (n : ℤ) (x : ParityPair n) :
    ‖x‖ ^ 2 = ∑' i : Bool × Sector n, ‖parityPairRepr n x i‖ ^ 2 := by
  rw [← (parityPairRepr n).norm_map]
  have h := lp.norm_rpow_eq_tsum (p := (2 : ℝ≥0∞)) (by norm_num)
    (parityPairRepr n x)
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using h

/-- The actual first-field DVP coefficient after the resonant projection. -/
theorem freeResolventPotentialColumn_upper_repr_coefficient_prerequisite
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    parityPairRepr n
        (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
          (parityPairVector n (false, resonantIndex n))) (true, m) =
      freeResolventCoeff n z m *
        physicalFourier u₁ ((m.val + (resonantIndex n).val) / 2) := by
  rw [parityPairRepr_inner]
  simpa using freeResolventPotentialColumn_upper_entry
    u₁ u₂ hu₁ hu₂ n z hz m (resonantIndex n)

/-- The actual reflected second-field DVP coefficient after projection. -/
theorem freeResolventPotentialColumn_lower_repr_coefficient_prerequisite
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (m : Sector n) :
    parityPairRepr n
        (freeResolventPotentialColumn u₁ u₂ hu₁ hu₂ n z hz
          (parityPairVector n (true, resonantIndex n))) (false, m) =
      freeResolventCoeff n z m *
        physicalFourier u₂ (-(m.val + (resonantIndex n).val) / 2) := by
  rw [parityPairRepr_inner]
  simpa using freeResolventPotentialColumn_lower_entry
    u₁ u₂ hu₁ hu₂ n z hz m (resonantIndex n)

end NlsGge.Schur
