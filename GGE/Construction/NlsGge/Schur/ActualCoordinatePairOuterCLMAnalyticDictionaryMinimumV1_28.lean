import NlsGge.Schur.ActualCoordinatePairConjugacyContinuousLinearMapDictionaryV1_27
import NlsGge.Schur.ActualCoordinateEndomorphismNormedModuleCoherenceMinimumV1_28
import NlsGge.Schur.ActualCoordinatePairEndomorphismModuleCoherenceMinimumV1_28
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

private abbrev ActualCoordinatePairOuterCLMExplicit28
    (n : ℤ)
    (sourceModule : Module ℂ (SectorSquare n →L[ℂ] SectorSquare n))
    (targetModule : Module ℂ (ParityPair n →L[ℂ] ParityPair n)) :=
  @ContinuousLinearMap ℂ ℂ
    Field.toSemifield.toSemiring Field.toSemifield.toSemiring
    (RingHom.id ℂ)
    (SectorSquare n →L[ℂ] SectorSquare n)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    ContinuousLinearMap.toNormedAddCommGroup.toAddCommMonoid
    (ParityPair n →L[ℂ] ParityPair n)
    PseudoMetricSpace.toUniformSpace.toTopologicalSpace
    NormedAddCommGroup.toAddCommGroup.toAddCommMonoid
    sourceModule targetModule

private abbrev ActualCoordinatePairAnalyticExpectedOuterCLM28 (n : ℤ) :=
  (SectorSquare n →L[ℂ] SectorSquare n) →L[ℂ]
    (ParityPair n →L[ℂ] ParityPair n)

/-- The explicit CLM carrier with the operator-NormedSpace scalar modules is
definitionally the outer CLM type appearing in the pinned analytic
postcomposition theorem. This checks the complete outer CLM parameters
(scalar semirings, ring homomorphism, topologies, additive monoids, and both
modules) independently of any analytic-family proof. -/
theorem actualCoordinatePairOuterCLM_explicit_eq_analyticExpectedV1_28
    (n : ℤ) :
    ActualCoordinatePairOuterCLMExplicit28 n
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n)).toModule =
    ActualCoordinatePairAnalyticExpectedOuterCLM28 n := by
  rfl

/-- The genuine Fourier arrow-conjugation CLM, transported only along the
checked source and target module equalities, has the exact explicit outer
CLM type above. This is a type/action prerequisite, not an analytic result. -/
noncomputable def actualCoordinatePairOuterCLMNormedV1_28 (n : ℤ) :
    ActualCoordinatePairOuterCLMExplicit28 n
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (SectorSquare n →L[ℂ] SectorSquare n)).toModule
      (ContinuousLinearMap.toNormedSpace :
        NormedSpace ℂ (ParityPair n →L[ℂ] ParityPair n)).toModule := by
  let source := SectorSquare n →L[ℂ] SectorSquare n
  let target := ParityPair n →L[ℂ] ParityPair n
  let sourceAmbient : Module ℂ source := ContinuousLinearMap.module
  let targetAmbient : Module ℂ target := ContinuousLinearMap.module
  let sourceNormed : Module ℂ source :=
    (ContinuousLinearMap.toNormedSpace : NormedSpace ℂ source).toModule
  let targetNormed : Module ℂ target :=
    (ContinuousLinearMap.toNormedSpace : NormedSpace ℂ target).toModule
  have hsource : sourceAmbient = sourceNormed := by
    calc
      sourceAmbient =
          (CStarAlgebra.toNonUnitalCStarAlgebra source).toModule := by
            simpa only [sourceAmbient, source] using
              actualCoordinateEndomorphismModule_eq_cstarV1_28 n
      _ = sourceNormed := by
            simpa only [sourceNormed, source] using
              (actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 n).symm
  have htarget : targetAmbient = targetNormed := by
    simpa only [targetAmbient, targetNormed, target] using
      actualPairEndomorphismModule_eq_normedV1_28 n
  have htype :
      ActualCoordinatePairOuterCLMExplicit28 n sourceAmbient targetAmbient =
        ActualCoordinatePairOuterCLMExplicit28 n sourceNormed targetNormed := by
    cases hsource
    cases htarget
    rfl
  let Ψambient : ActualCoordinatePairOuterCLMExplicit28 n sourceAmbient targetAmbient :=
    (((parityPairRepr n).toContinuousLinearEquiv.symm.arrowCongr
      (parityPairRepr n).toContinuousLinearEquiv.symm).toContinuousLinearMap)
  exact htype ▸ Ψambient

/-- The transported outer CLM is exactly the public actual conjugacy CLM,
not merely a map with an assumed matching conclusion. -/
theorem actualCoordinatePairOuterCLMNormed_eq_publicCLMV1_28 (n : ℤ) :
    actualCoordinatePairOuterCLMNormedV1_28 n =
      actualCoordinatePairConjugacyContinuousLinearMapV1_27 n := by
  unfold actualCoordinatePairOuterCLMNormedV1_28
  dsimp only
  let source := SectorSquare n →L[ℂ] SectorSquare n
  let target := ParityPair n →L[ℂ] ParityPair n
  let sourceAmbient : Module ℂ source := ContinuousLinearMap.module
  let targetAmbient : Module ℂ target := ContinuousLinearMap.module
  let sourceNormed : Module ℂ source :=
    (ContinuousLinearMap.toNormedSpace : NormedSpace ℂ source).toModule
  let targetNormed : Module ℂ target :=
    (ContinuousLinearMap.toNormedSpace : NormedSpace ℂ target).toModule
  have hsource : sourceAmbient = sourceNormed := by
    calc
      sourceAmbient =
          (CStarAlgebra.toNonUnitalCStarAlgebra source).toModule := by
            simpa only [sourceAmbient, source] using
              actualCoordinateEndomorphismModule_eq_cstarV1_28 n
      _ = sourceNormed := by
            simpa only [sourceNormed, source] using
              (actualCoordinateEndomorphismNormedModule_eq_cstarV1_28 n).symm
  have htarget : targetAmbient = targetNormed := by
    simpa only [targetAmbient, targetNormed, target] using
      actualPairEndomorphismModule_eq_normedV1_28 n
  have htype :
      ActualCoordinatePairOuterCLMExplicit28 n sourceAmbient targetAmbient =
        ActualCoordinatePairOuterCLMExplicit28 n sourceNormed targetNormed := by
    cases hsource
    cases htarget
    rfl
  cases hsource
  cases htarget
  change
    (((parityPairRepr n).toContinuousLinearEquiv.symm.arrowCongr
      (parityPairRepr n).toContinuousLinearEquiv.symm).toContinuousLinearMap) =
      actualCoordinatePairConjugacyContinuousLinearMapV1_27 n
  exact (actualCoordinatePairConjugacyContinuousLinearMap_eq_arrowCongrV1_27 n).symm

end NlsGge.Schur
