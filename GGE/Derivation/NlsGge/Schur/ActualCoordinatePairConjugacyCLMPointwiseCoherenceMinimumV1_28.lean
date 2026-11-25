import NlsGge.Schur.ActualCoordinatePairConjugacyContinuousLinearMapDictionaryV1_27

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

/-- The public CLM representative and the actual Fourier-isometry algebra
conjugacy have the same action on every paired vector. The proof uses the
checked pointwise action of the CLM representative and extensionality on the
actual paired carrier. -/
theorem actualCoordinatePairConjugacyCLM_eq_endomorphismConjugacy_pointwiseV1_28
    (n : ℤ) (T : SectorSquare n →L[ℂ] SectorSquare n) :
    actualCoordinatePairConjugacyContinuousLinearMapV1_27 n T =
      actualCoordinatePairEndomorphismConjugacyV2_26 n T := by
  ext x
  rw [actualCoordinatePairConjugacyContinuousLinearMap_applyV1_27]
  rfl

end NlsGge.Schur
