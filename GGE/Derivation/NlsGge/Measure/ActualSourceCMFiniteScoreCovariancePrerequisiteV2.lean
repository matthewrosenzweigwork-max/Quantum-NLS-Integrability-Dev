import NlsGge.Measure.ActualSourceCMFiniteScoreEvaluationPrerequisiteV1
import NlsGge.Measure.ModeDualCovariance

set_option autoImplicit false
noncomputable section
open scoped RealInnerProductSpace

namespace NlsGge.Measure

theorem actualSourceCMFiniteScoreFunctional_covarianceTerm_v1
    {lower upper : ℝ} (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (x : NlsGge.Pilot.WeightedRealHilbert (NlsGge.Pilot.cmModeWeight c))
    (n : ℤ) :
    fullWeightedDualCovarianceTerm c 0
      (actualSourceCMFiniteScoreFunctional c x)
      (actualSourceCMFiniteScoreFunctional c x) n =
      NlsGge.Pilot.cmModeWeight c n *
        ‖(show NlsGge.Pilot.WeightedHilbert
          (NlsGge.Pilot.cmModeWeight c) from x) n‖ ^ 2 := by
  rw [fullWeightedDualCovarianceTerm,
    actualSourceCMFiniteScoreFunctional_modeEvaluation_v1 c x n 1,
    actualSourceCMFiniteScoreFunctional_modeEvaluation_v1 c x n Complex.I]
  have hre : inner ℝ
      ((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n) (1 : ℂ) =
      ((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n).re := by
    simp [Complex.inner]
  have him : inner ℝ
      ((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n) Complex.I =
      ((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n).im := by
    simp [Complex.inner]
  rw [hre, him, NlsGge.Pilot.cmModeWeight]
  have hnorm : ‖(show NlsGge.Pilot.WeightedHilbert
      (NlsGge.Pilot.cmModeWeight c) from x) n‖ ^ 2 =
      (((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n).re) ^ 2 +
      (((show NlsGge.Pilot.WeightedHilbert
        (NlsGge.Pilot.cmModeWeight c) from x) n).im) ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply]
    ring
  rw [hnorm]
  have hrate : NlsGge.Pilot.sourceRate c n ≠ 0 :=
    (NlsGge.Pilot.sourceRate_pos c n).ne'
  field_simp

end NlsGge.Measure
