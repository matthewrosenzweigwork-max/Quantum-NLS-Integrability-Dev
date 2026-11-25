import NlsGge.Measure.FiniteProjectionAE
import NlsGge.Measure.PhysicalWeightedLaw
import NlsGge.Measure.ScalarGaussianMoments
import NlsGge.Sobolev.PhysicalProjection
import Mathlib.Analysis.Normed.Operator.Basic

set_option autoImplicit false
noncomputable section
open MeasureTheory ProbabilityTheory

namespace NlsGge.Measure

local instance instFullWeightedDualNormPrerequisites {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :=
  (ContinuousLinearMap.hasOpNorm :
    Norm (NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ))

lemma fullWeightedSequenceGaussian_map_projectionScalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (N : ℕ)
    (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    (NlsGge.Measure.fullWeightedSequenceGaussian c s).map
      (fun x => L (NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N) x)) =
    (NlsGge.Measure.fullWeightSequenceGaussian c.val).map
      (fun z => L (NlsGge.Measure.fullWeightedSequencePartial c s N z)) := by
  have hproj : Measurable (fun x : NlsGge.Pilot.FullWeightedHilbert c s =>
      L (NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N) x)) := by
    fun_prop
  unfold fullWeightedSequenceGaussian
  calc
    ((fullWeightSequenceGaussian c.val).map (fullWeightedSequenceRealization c s)).map
        (fun x => L (NlsGge.Pilot.weightedRealProjectionContinuous
          (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N) x)) =
      (fullWeightSequenceGaussian c.val).map
        (fun z => L (NlsGge.Pilot.weightedRealProjectionContinuous
          (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N)
          (fullWeightedSequenceRealization c s z))) := by
            rw [Measure.map_map hproj (measurable_fullWeightedSequenceRealization c s)]
            rfl
    _ = (fullWeightSequenceGaussian c.val).map
        (fun z => L (fullWeightedSequencePartial c s N z)) := by
          exact Measure.map_congr
            (ae_fullWeightedSequencePartial_dual_eq_weightedRealProjection c s hs N L).symm

lemma integrable_fullWeightedSequenceGaussian_norm {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) :
    MeasureTheory.Integrable
      (fun x : NlsGge.Pilot.FullWeightedHilbert c s => ‖x‖)
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have hnormLp : MeasureTheory.MemLp
      (fun x : NlsGge.Pilot.FullWeightedHilbert c s => ‖x‖) 2
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
    exact (memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_fullWeightedSequenceGaussian_sqNorm c s hs)
  exact hnormLp.integrable (by norm_num)

lemma memLp_fullWeightedSequenceGaussian_scalar {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (L : NlsGge.Pilot.FullWeightedHilbert c s →L[ℝ] ℝ) :
    MeasureTheory.MemLp L 2 (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
  have hnormLp : MeasureTheory.MemLp
      (fun x : NlsGge.Pilot.FullWeightedHilbert c s => ‖x‖) 2
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) := by
    exact (memLp_two_iff_integrable_sq (by fun_prop)).2
      (integrable_fullWeightedSequenceGaussian_sqNorm c s hs)
  have hboundLp : MeasureTheory.MemLp
      (fun x : NlsGge.Pilot.FullWeightedHilbert c s => ‖L‖ * ‖x‖) 2
      (NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    hnormLp.const_mul ‖L‖
  exact hboundLp.mono' (by fun_prop) (Filter.Eventually.of_forall fun x => L.le_opNorm x)

end NlsGge.Measure
