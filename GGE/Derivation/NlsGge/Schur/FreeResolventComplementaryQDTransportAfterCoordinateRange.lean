import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.FreeResolventComplementaryCoordinateRangeMinimalRevised

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Fourier-coordinate complement transported to the actual paired physical
carrier. Its body is the checked construction used by the square-bound source. -/
def freeResolventComplementaryProjectionTransported (n : ℤ) :
    ParityPair n →L[ℂ] ParityPair n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
    ((complementarySquare n).comp
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Transport the checked coordinate fact that the free-resolvent output has
zero resonant coefficient to the actual paired physical carrier. -/
theorem freeResolventParityPair_comp_complementaryProjection_afterCoordinateRange
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (freeResolventComplementaryProjectionTransported n).comp
      (freeResolventParityPair n z hz) = freeResolventParityPair n z hz := by
  let E := parityPairRepr n
  apply ContinuousLinearMap.ext
  intro x
  apply E.injective
  change E (E.symm (complementarySquare n
      (E (E.symm (freeResolventSquare n z hz (E x)))))) =
    E (E.symm (freeResolventSquare n z hz (E x)))
  simp only [E.apply_symm_apply]
  exact complementarySquare_freeResolventSquare_fixed n z hz (E x)

end NlsGge.Schur
