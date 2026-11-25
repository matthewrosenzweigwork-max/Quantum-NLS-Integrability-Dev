import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.FreeResolventComplementaryQDTransportAfterCoordinateRange

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The free diagonal also fixes the complementary-coordinate input on the
right: its resonant coefficient is zero, while Q is the identity elsewhere. -/
theorem freeResolventSquare_complementarySquare_fixed
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) (y : SectorSquare n) :
    freeResolventSquare n z hz (complementarySquare n y) =
      freeResolventSquare n z hz y := by
  apply lp.ext
  funext i
  simp only [freeResolventSquare_apply, complementarySquare_apply]
  by_cases hi : i.2 = resonantIndex n
  · simp [hi, freeResolventCoeff]
  · simp [hi]

/-- Transport the checked coordinate identity through the actual Fourier
isometry. This is the right-support property `D Q = D`, kept distinct from
`Q D = D`. -/
theorem freeResolventParityPair_comp_complementaryProjection_right_afterCoordinateRange
    (n : ℤ) (z : ℂ) (hz : z ∈ spectralDisk n) :
    (freeResolventParityPair n z hz).comp
      (freeResolventComplementaryProjectionTransported n) =
    freeResolventParityPair n z hz := by
  let E := parityPairRepr n
  apply ContinuousLinearMap.ext
  intro x
  apply E.injective
  change E (E.symm (freeResolventSquare n z hz
      (E (E.symm (complementarySquare n (E x)))))) =
    E (E.symm (freeResolventSquare n z hz (E x)))
  simp only [E.apply_symm_apply]
  exact freeResolventSquare_complementarySquare_fixed n z hz (E x)

end NlsGge.Schur
