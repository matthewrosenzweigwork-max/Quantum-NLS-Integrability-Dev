import NlsGge.Schur.ActualSchurCoordinateTransposePrerequisites23
import Mathlib.Analysis.InnerProductSpace.Adjoint

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- Transport the actual square-coordinate conjugation to the genuine paired
parity carrier through its complete Fourier unitary. -/
def actualPairTransposeConjugationAfterCoordinate23 (n : ℤ) :
    ParityPair n →SL[starRingEnd ℂ] ParityPair n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap :
      SectorSquare n →SL[RingHom.id ℂ] ParityPair n) ∘SL
    ((actualCoordinateConjugation23 n) ∘SL
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap :
        ParityPair n →SL[RingHom.id ℂ] SectorSquare n))

/-- The transported conjugation exchanges the two actual parity basis
coordinates, as verified first on the square carrier. -/
@[simp] theorem actualPairTransposeConjugationAfterCoordinate23_basis
    (n : ℤ) (b : Bool) (m : Sector n) :
    actualPairTransposeConjugationAfterCoordinate23 n (parityPairVector n (b, m)) =
      parityPairVector n (!b, m) := by
  let e := parityPairRepr n
  apply e.injective
  change e (e.symm (actualCoordinateConjugation23 n
    (e (parityPairVector n (b, m))))) = e (parityPairVector n (!b, m))
  rw [e.apply_symm_apply, parityPairRepr_vector,
    actualCoordinateConjugation23_single, parityPairRepr_vector]

theorem actualPairTransposeConjugationAfterCoordinate23_involutive
    (n : ℤ) (x : ParityPair n) :
    actualPairTransposeConjugationAfterCoordinate23 n
      (actualPairTransposeConjugationAfterCoordinate23 n x) = x := by
  let e := parityPairRepr n
  apply e.injective
  change e (e.symm (actualCoordinateConjugation23 n
    (e (e.symm (actualCoordinateConjugation23 n (e x)))))) = e x
  simp only [e.apply_symm_apply]
  exact actualCoordinateConjugation23_involutive n (e x)

/-- Transport a physical endomorphism to the actual square Fourier carrier. -/
private def actualPairEndomorphismToSquareAfterCoordinate23 (n : ℤ)
    (T : ParityPair n →L[ℂ] ParityPair n) : SectorSquare n →L[ℂ] SectorSquare n :=
  ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap).comp
    (T.comp
      ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap))

private theorem actualPairEndomorphismToSquareAfterCoordinate23_comp (n : ℤ)
    (T S : ParityPair n →L[ℂ] ParityPair n) :
    actualPairEndomorphismToSquareAfterCoordinate23 n (T.comp S) =
      (actualPairEndomorphismToSquareAfterCoordinate23 n T).comp
        (actualPairEndomorphismToSquareAfterCoordinate23 n S) := by
  apply ContinuousLinearMap.ext
  intro x
  simp [actualPairEndomorphismToSquareAfterCoordinate23,
    ContinuousLinearMap.comp_apply]

/-- The actual parity-pair transpose is the coordinate transpose conjugated
by the complete Fourier unitary. -/
def actualPairTransposeAfterCoordinate23 (n : ℤ)
    (T : ParityPair n →L[ℂ] ParityPair n) : ParityPair n →L[ℂ] ParityPair n :=
  ((parityPairRepr n).toContinuousLinearEquiv.symm.toContinuousLinearMap).comp
    ((actualCoordinateTranspose23 n
      (actualPairEndomorphismToSquareAfterCoordinate23 n T)).comp
      ((parityPairRepr n).toContinuousLinearEquiv.toContinuousLinearMap))

/-- Product reversal for the physical transpose follows from the square
coordinate identity and the explicit unitary cancellation maps. -/
theorem actualPairTransposeAfterCoordinate23_comp (n : ℤ)
    (T S : ParityPair n →L[ℂ] ParityPair n) :
    actualPairTransposeAfterCoordinate23 n (T.comp S) =
      (actualPairTransposeAfterCoordinate23 n S).comp
        (actualPairTransposeAfterCoordinate23 n T) := by
  apply ContinuousLinearMap.ext
  intro x
  let e := parityPairRepr n
  change e.symm (actualCoordinateTranspose23 n
      (actualPairEndomorphismToSquareAfterCoordinate23 n (T.comp S)) (e x)) =
    e.symm (actualCoordinateTranspose23 n
      (actualPairEndomorphismToSquareAfterCoordinate23 n S)
        (e (e.symm (actualCoordinateTranspose23 n
          (actualPairEndomorphismToSquareAfterCoordinate23 n T) (e x)))))
  rw [actualPairEndomorphismToSquareAfterCoordinate23_comp,
    actualCoordinateTranspose23_comp]
  simp only [ContinuousLinearMap.comp_apply, e.apply_symm_apply]

end NlsGge.Schur
