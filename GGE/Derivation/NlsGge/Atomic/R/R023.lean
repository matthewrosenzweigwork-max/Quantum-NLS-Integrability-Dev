import Mathlib
import NlsGge.Ramer.TruncatedFieldConvergence
import NlsGge.Ramer.RamerJacobianHead
import NlsGge.Ramer.RamerJacobianLimits
import NlsGge.Ramer.RamerStep8a
import NlsGge.Ramer.CameronMartinE
import NlsGge.Ramer.ProjFieldNullPreserving
import NlsGge.Ramer.RamerLocalLowerBound

/- R-023 PROOF01 (proof development, AUTHOR; not self-reviewed).  Pro's shared concrete hosts (RamerE, RamerH, ramerGaussian, coordinateGaussian,
   cmEmbedding, ambientProjection, truncField, projField, TM, hsDerivH, ramerJac) and the R-023 head verbatim from
   gpt6pro_followup2/.../PRO_DEFINITION_RESPONSE_FP80_02_03.md (commit 1b36c77b); elaboration probe RAMER_PROBE01 (fa75d40f) passed unchanged.
   Route: production NlsGge.Ramer.tendsto_eLpNorm_truncatedField (TruncatedFieldConvergence.lean:145, raw Gaussian space) transported to E_s:
   ramerGaussian c s = map R γ (R the measurable realization), eLpNorm_map_measure (continuous integrand), and the a.e. identity of realized
   coordinates (ae_fullWeightedSequenceRealization_apply) with headToE_headPt_eq. -/
set_option autoImplicit false

open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators RealInnerProductSpace

namespace NlsGge.ThirdConsultation.R
noncomputable section

abbrev RamerE {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :=
  NlsGge.Pilot.FullWeightedHilbert c s

abbrev RamerH {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) :=
  NlsGge.Ramer.ActualCM c

def ramerGaussian {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ) :
    Measure (RamerE c s) :=
  NlsGge.Measure.fullWeightedSequenceGaussian c s

def coordinateGaussian {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) :
    Measure (ℤ → ℂ) :=
  NlsGge.Measure.fullWeightSequenceGaussian c.val

def cmEmbedding {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) : RamerH c →L[ℝ] RamerE c s :=
  NlsGge.Ramer.inclE c s hs

def ambientProjection {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ) (x : RamerE c s) : RamerE c s :=
  show NlsGge.Pilot.FullWeightedHilbert c s from
    NlsGge.Pilot.weightedProjection
      (NlsGge.Pilot.fullModeWeight c s)
      (NlsGge.Pilot.symmetricModes N) x

def truncField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (G : RamerE c s → RamerH c) (N : ℕ) :
    RamerE c s → RamerH c :=
  fun x => NlsGge.Ramer.headProj c N (G (ambientProjection c s N x))

def projField {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (N : ℕ) (K : RamerE c s → RamerH c) :
    RamerE c s → RamerH c :=
  fun x => NlsGge.Ramer.headProj c N (K x)

def TM {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s) (K : RamerE c s → RamerH c) :
    RamerE c s → RamerE c s :=
  fun x => x + cmEmbedding c s hs (K x)

def hsDerivH {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : RamerE c s → RamerH c) (x : RamerE c s) :
    NlsGge.Analysis.RegularizedDeterminant.HilbertSchmidt
      (RamerH c) (RamerH c) :=
  NlsGge.Ramer.hsDerivH c s hs K x

def ramerJac {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper) (s : ℝ)
    (hs : (1 : ℝ) / 2 < s)
    (K : RamerE c s → RamerH c) (x : RamerE c s) : ℝ :=
  |NlsGge.Analysis.RegularizedDeterminant.det2 (hsDerivH c s hs K x)| *
    Real.exp (-(NlsGge.Ramer.ramerDiv c s hs K
      (NlsGge.Ramer.coordE c s x)) - ‖K x‖ ^ 2 / 2)


theorem tendsto_eLpNorm_truncatedField
    {lower upper : ℝ}
    (c : NlsGge.Pilot.BoundedCoefficients lower upper)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s)
    (G : RamerE c s → RamerH c) (hG : Continuous G)
    (M : ℝ) (hB : ∀ x : RamerE c s, ‖G x‖ ≤ M) :
    Tendsto
      (fun N : ℕ =>
        eLpNorm (fun x : RamerE c s => truncField c s G N x - G x)
          2 (ramerGaussian c s))
      atTop (𝓝 0) := by
  have hprod := NlsGge.Ramer.tendsto_eLpNorm_truncatedField c s hs G hG M hB
  have hRm := NlsGge.Measure.measurable_fullWeightedSequenceRealization c s
  have hae := NlsGge.Measure.ae_fullWeightedSequenceRealization_apply c s hs
  have hproj : ∀ N : ℕ, Continuous (ambientProjection c s N) := fun N => by
    have : ambientProjection c s N = ⇑(NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N)) := rfl
    rw [this]
    exact (NlsGge.Pilot.weightedRealProjectionContinuous
        (NlsGge.Pilot.fullModeWeight c s) (NlsGge.Pilot.symmetricModes N)).continuous
  have hcont : ∀ N : ℕ, Continuous (fun x : RamerE c s => truncField c s G N x - G x) := fun N =>
    (((NlsGge.Ramer.headProj c N).continuous.comp (hG.comp (hproj N)))).sub hG
  have key : ∀ N : ℕ,
      eLpNorm (fun x : RamerE c s => truncField c s G N x - G x) 2 (ramerGaussian c s) =
      eLpNorm (fun z => ‖NlsGge.Ramer.cylField c N
          (fun v => NlsGge.Ramer.cmTrunc c N (G (NlsGge.Ramer.headToE c s N v))) z -
          G (NlsGge.Measure.fullWeightedSequenceRealization c s z)‖) 2
        (NlsGge.Measure.fullWeightSequenceGaussian c.val) := by
    intro N
    have hnorm : eLpNorm (fun x : RamerE c s => truncField c s G N x - G x) 2 (ramerGaussian c s) =
        eLpNorm (fun x : RamerE c s => ‖truncField c s G N x - G x‖) 2 (ramerGaussian c s) := by
      have hf1 : AEStronglyMeasurable (fun x : RamerE c s => truncField c s G N x - G x)
          (ramerGaussian c s) := (hcont N).aestronglyMeasurable
      exact (eLpNorm_norm _ hf1).symm
    rw [hnorm]
    show eLpNorm (fun x : RamerE c s => ‖truncField c s G N x - G x‖) 2
      (Measure.map (NlsGge.Measure.fullWeightedSequenceRealization c s)
        (NlsGge.Measure.fullWeightSequenceGaussian c.val)) = _
    have haes : AEStronglyMeasurable (fun x : RamerE c s => ‖truncField c s G N x - G x‖)
        (Measure.map (NlsGge.Measure.fullWeightedSequenceRealization c s)
          (NlsGge.Measure.fullWeightSequenceGaussian c.val)) :=
      (hcont N).norm.aestronglyMeasurable
    rw [eLpNorm_map_measure haes hRm.aemeasurable]
    refine eLpNorm_congr_ae ?_
    filter_upwards [hae] with z hz
    simp only [Function.comp]
    have e : NlsGge.Ramer.cylField c N
        (fun v => NlsGge.Ramer.cmTrunc c N (G (NlsGge.Ramer.headToE c s N v))) z =
        truncField c s G N (NlsGge.Measure.fullWeightedSequenceRealization c s z) := by
      unfold NlsGge.Ramer.cylField truncField ambientProjection
      beta_reduce
      rw [NlsGge.Ramer.headToE_headPt_eq c s N z hz, NlsGge.Ramer.headProj_apply]
    rw [e]
  simpa only [key] using hprod

end
end NlsGge.ThirdConsultation.R
