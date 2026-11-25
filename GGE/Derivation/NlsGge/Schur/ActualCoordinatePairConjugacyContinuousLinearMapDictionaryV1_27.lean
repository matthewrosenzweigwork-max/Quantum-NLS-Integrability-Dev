import NlsGge.Schur.FreeResolventPotentialBlocks
import NlsGge.Schur.ActualCoordinatePairCenterFactorConjugacyV2_26
import Mathlib.Analysis.Normed.Operator.ContinuousAlgEquiv

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The concrete continuous-linear-map representative of the already checked
Fourier-isometry algebra conjugacy.  This isolates the CLM coercion used by
analytic postcomposition from the inverse and analytic-family arguments. -/
def actualCoordinatePairConjugacyContinuousLinearMapV1_27 (n : ℤ) :
    (SectorSquare n →L[ℂ] SectorSquare n) →L[ℂ]
      (ParityPair n →L[ℂ] ParityPair n) :=
  (actualCoordinatePairEndomorphismConjugacyV2_26 n).toContinuousLinearEquiv.toContinuousLinearMap

/-- The CLM coercion has the actual Fourier-conjugation action on every
coordinate endomorphism and paired vector. -/
theorem actualCoordinatePairConjugacyContinuousLinearMap_applyV1_27
    (n : ℤ) (T : SectorSquare n →L[ℂ] SectorSquare n)
    (x : ParityPair n) :
    actualCoordinatePairConjugacyContinuousLinearMapV1_27 n T x =
      (parityPairRepr n).symm (T (parityPairRepr n x)) := by
  rfl

/-- The algebra-equivalence CLM and the direct arrow-conjugation CLM are the
same map on the actual paired and coordinate endomorphism spaces. -/
theorem actualCoordinatePairConjugacyContinuousLinearMap_eq_arrowCongrV1_27
    (n : ℤ) :
    actualCoordinatePairConjugacyContinuousLinearMapV1_27 n =
      (((parityPairRepr n).toContinuousLinearEquiv.symm.arrowCongr
        (parityPairRepr n).toContinuousLinearEquiv.symm).toContinuousLinearMap) := by
  rfl

end NlsGge.Schur
