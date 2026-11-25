import NlsGge.Schur.ActualCoordinatePairOuterCLMAnalyticDictionaryMinimumV1_28
import NlsGge.Schur.ActualCoordinatePairConjugacyCLMPointwiseCoherenceMinimumV1_28
import Mathlib.Analysis.Analytic.Basic

set_option autoImplicit false
noncomputable section

namespace NlsGge.Schur

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1000000 in
/-- Postcomposition by the actual Fourier-conjugation map preserves
analyticity for an arbitrary family on the coordinate endomorphism carrier.
The outer CLM uses the exact operator-NormedSpace dictionaries required by
the analytic composition theorem; its action is identified with the actual
algebra conjugacy by checked pointwise equalities. This is an analytic
transport prerequisite only, not analyticity of a particular inverse family
or moving Schur center. -/
theorem actualCoordinatePairConjugacy_analyticOnNhdV3_29
    (n : ℤ) (s : Set ℂ)
    (f : ℂ → SectorSquare n →L[ℂ] SectorSquare n)
    (hf : AnalyticOnNhd ℂ f s) :
    AnalyticOnNhd ℂ
      (fun z => actualCoordinatePairEndomorphismConjugacyV2_26 n (f z)) s := by
  have hΨ : actualCoordinatePairOuterCLMNormedV1_28 n =
      actualCoordinatePairConjugacyContinuousLinearMapV1_27 n :=
    actualCoordinatePairOuterCLMNormed_eq_publicCLMV1_28 n
  have hpost : AnalyticOnNhd ℂ
      (fun z => actualCoordinatePairOuterCLMNormedV1_28 n (f z)) s := by
    exact ContinuousLinearMap.comp_analyticOnNhd
      (𝕜 := ℂ) (E := ℂ)
      (F := SectorSquare n →L[ℂ] SectorSquare n)
      (G := ParityPair n →L[ℂ] ParityPair n)
      (g := actualCoordinatePairOuterCLMNormedV1_28 n)
      (f := f) (s := s) hf
  have hfun :
      (fun z => actualCoordinatePairOuterCLMNormedV1_28 n (f z)) =
        (fun z => actualCoordinatePairEndomorphismConjugacyV2_26 n (f z)) := by
    funext z
    exact
      (congrArg (fun L => L (f z)) hΨ).trans
        (actualCoordinatePairConjugacyCLM_eq_endomorphismConjugacy_pointwiseV1_28
          n (f z))
  rw [hfun] at hpost
  exact hpost

end NlsGge.Schur
