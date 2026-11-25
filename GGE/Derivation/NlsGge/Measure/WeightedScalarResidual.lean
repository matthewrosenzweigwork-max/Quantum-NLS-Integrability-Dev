import NlsGge.Measure.WeightedScalarPrerequisites
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NlsGge.Measure

local instance instFullWeightedDualNormResidual {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :=
  (ContinuousLinearMap.hasOpNorm :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ))

lemma integrable_fullWeightedProjectionScalar_residual {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    MeasureTheory.Integrable (fun x : NlsGge.Pilot.FullWeightedHilbert c s =>
      ‖L (NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N) x) - L x‖)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  let P : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ]
      NlsGge.Pilot.FullWeightedHilbert c s :=
    NlsGge.Pilot.weightedRealProjectionContinuous
      (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N)
  have hProj : MeasureTheory.MemLp (L.comp P) 2
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    NlsGge.Measure.memLp_fullWeightedSequenceGaussian_scalar c s hs (L.comp P)
  have hL : MeasureTheory.MemLp L 2
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    NlsGge.Measure.memLp_fullWeightedSequenceGaussian_scalar c s hs L
  have hProjInt : MeasureTheory.Integrable (L.comp P)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    hProj.integrable (by norm_num)
  have hLInt : MeasureTheory.Integrable L
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    hL.integrable (by norm_num)
  have hDiff : MeasureTheory.Integrable (fun x : NlsGge.Pilot.FullWeightedHilbert c s =>
      L (P x) - L x) (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
    exact hProjInt.sub hLInt
  exact hDiff.norm

end NlsGge.Measure
