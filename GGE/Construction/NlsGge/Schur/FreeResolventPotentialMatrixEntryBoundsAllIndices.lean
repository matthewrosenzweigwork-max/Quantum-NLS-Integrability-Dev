import NlsGge.Schur.FreeResolventPotentialMatrixEntryBoundsAfterInnerScalar

set_option autoImplicit false
noncomputable section
open scoped InnerProduct InnerProductSpace

namespace NlsGge.Schur
open NlsGge.Pilot NlsGge.Analysis

private theorem sectorIndex_zero_eq_resonant (n : ℤ) :
    sectorIndex n 0 = resonantIndex n := by
  apply Subtype.ext
  change n + 2 * 0 = n
  ring

/-- The upper DVD coefficient estimate extends across the resonant index:
when either free factor is resonant the actual entry and source weight both
vanish. -/
theorem freeResolventPotentialFreeResolvent_upper_entry_sq_bound_all
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (r s : ℤ) :
    ‖inner ℂ (parityPairVector n (true, sectorIndex n r))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (false, sectorIndex n s)))‖ ^ 2 ≤
      ‖physicalFourier u₁ (n + r + s)‖ ^ 2 *
        inverseSquare r * inverseSquare s := by
  by_cases hr : r = 0
  · subst r
    rw [freeResolventPotentialFreeResolvent_upper_entry]
    simp [sectorIndex_zero_eq_resonant, freeResolventCoeff, inverseSquare]
  · by_cases hs : s = 0
    · subst s
      rw [freeResolventPotentialFreeResolvent_upper_entry]
      simp [sectorIndex_zero_eq_resonant, freeResolventCoeff, inverseSquare]
    · exact freeResolventPotentialFreeResolvent_upper_entry_sq_bound
        u₁ u₂ hu₁ hu₂ n z hz r s hr hs

/-- The independent reflected lower DVD coefficient estimate extends across
the resonant index by the same actual vanishing free factors. -/
theorem freeResolventPotentialFreeResolvent_lower_entry_sq_bound_all
    (u₁ u₂ : PhysicalL2)
    (hu₁ : SobolevSquareSummable 1 (physicalFourier u₁))
    (hu₂ : SobolevSquareSummable 1 (physicalFourier u₂))
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (r s : ℤ) :
    ‖inner ℂ (parityPairVector n (false, sectorIndex n r))
      (freeResolventPotentialFreeResolvent u₁ u₂ hu₁ hu₂ n z hz
        (parityPairVector n (true, sectorIndex n s)))‖ ^ 2 ≤
      ‖physicalFourier u₂ (-(n + r + s))‖ ^ 2 *
        inverseSquare r * inverseSquare s := by
  by_cases hr : r = 0
  · subst r
    rw [freeResolventPotentialFreeResolvent_lower_entry]
    simp [sectorIndex_zero_eq_resonant, freeResolventCoeff, inverseSquare]
  · by_cases hs : s = 0
    · subst s
      rw [freeResolventPotentialFreeResolvent_lower_entry]
      simp [sectorIndex_zero_eq_resonant, freeResolventCoeff, inverseSquare]
    · exact freeResolventPotentialFreeResolvent_lower_entry_sq_bound
        u₁ u₂ hu₁ hu₂ n z hz r s hr hs

end NlsGge.Schur
