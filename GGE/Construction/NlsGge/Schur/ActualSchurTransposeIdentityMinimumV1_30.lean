import NlsGge.Schur.ActualSchurCoordinateTransposePrerequisites23
import NlsGge.Schur.ActualPairTransposeTransportAfterCoordinatePrerequisite23

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

abbrev ActualSchurPairEndomorphismIdentityV1_30 (n : ℤ) :=
  ParityPair n →L[ℂ] ParityPair n

abbrev ActualSchurSquareEndomorphismIdentityV1_30 (n : ℤ) :=
  SectorSquare n →L[ℂ] SectorSquare n

/-- The actual endomorphism conjugacy from the physical parity-pair carrier
to its square Fourier representation, with both carrier types fixed here. -/
def actualSchurEndomorphismToSquareIdentityV1_30 (n : ℤ)
    (T : ActualSchurPairEndomorphismIdentityV1_30 n) :
    ActualSchurSquareEndomorphismIdentityV1_30 n :=
  (((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
      ParityPair n →L[ℂ] SectorSquare n).comp
    (T.comp ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →L[ℂ] ParityPair n)))

/-- The coordinate transpose fixes the actual identity on the square carrier.
The proof stays at continuous-map application level before invoking the
concrete conjugation involution. -/
theorem actualCoordinateTranspose23_one_identityMinimumV1_30 (n : ℤ) :
    actualCoordinateTranspose23 n
      (1 : ActualSchurSquareEndomorphismIdentityV1_30 n) = 1 := by
  apply ContinuousLinearMap.ext
  intro x
  change actualCoordinateConjugation23 n
    ((1 : ActualSchurSquareEndomorphismIdentityV1_30 n).adjoint
      (actualCoordinateConjugation23 n x)) = x
  rw [ContinuousLinearMap.adjoint_one]
  exact actualCoordinateConjugation23_involutive n x

/-- The actual Fourier coordinate maps compose to the identity on the square
carrier, at the exact pair/square continuous-map types used by the Schur map. -/
theorem actualSchurEndomorphismToSquare_one_identityMinimumV1_30 (n : ℤ) :
    actualSchurEndomorphismToSquareIdentityV1_30 n
      (1 : ActualSchurPairEndomorphismIdentityV1_30 n) = 1 := by
  let e := parityPairRepr n
  apply ContinuousLinearMap.ext
  intro x
  change e (e.symm x) = x
  exact e.apply_symm_apply x

/-- The true transpose on the pair carrier is transported from the square
coordinate transpose through the actual parity Fourier equivalence. -/
def actualSchurTransposeIdentityV1_30 (n : ℤ)
    (T : ActualSchurPairEndomorphismIdentityV1_30 n) :
    ActualSchurPairEndomorphismIdentityV1_30 n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →L[ℂ] ParityPair n).comp
    ((actualCoordinateTranspose23 n
      (actualSchurEndomorphismToSquareIdentityV1_30 n T)).comp
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
        ParityPair n →L[ℂ] SectorSquare n))

/-- The explicit coordinate-conjugacy helper is definitionally the repository's
actual transported transpose, so the exact public target can use this minimum. -/
theorem actualSchurTransposeIdentityV1_30_eq_actualPairTranspose (n : ℤ)
    (T : ActualSchurPairEndomorphismIdentityV1_30 n) :
    actualSchurTransposeIdentityV1_30 n T =
      actualPairTransposeAfterCoordinate23 n T := rfl

/-- The actual transported pair transpose fixes the identity endomorphism. -/
theorem actualPairTransposeAfterCoordinate23_one_identityMinimumV1_30 (n : ℤ) :
    actualPairTransposeAfterCoordinate23 n
      (1 : ActualSchurPairEndomorphismIdentityV1_30 n) = 1 := by
  rw [← actualSchurTransposeIdentityV1_30_eq_actualPairTranspose n 1]
  change
    ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →L[ℂ] ParityPair n).comp
    ((actualCoordinateTranspose23 n
      (actualSchurEndomorphismToSquareIdentityV1_30 n
        (1 : ActualSchurPairEndomorphismIdentityV1_30 n))).comp
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
        ParityPair n →L[ℂ] SectorSquare n)) = 1
  rw [actualSchurEndomorphismToSquare_one_identityMinimumV1_30,
    actualCoordinateTranspose23_one_identityMinimumV1_30]
  let e := parityPairRepr n
  apply ContinuousLinearMap.ext
  intro x
  change e.symm (e x) = x
  exact e.symm_apply_apply x

end NlsGge.Schur
