import Mathlib
import NlsGge.Measure.CountableReconstruction
import NlsGge.Birkhoff.W07Probability38
import NlsGge.Birkhoff.W10Localized38i
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.T.TDefsHost
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Atomic.T.T008
import NlsGge.Atomic.T.T009
import NlsGge.Atomic.T.T013
import NlsGge.ThirdConsultation.R.R100Host
import NlsGge.ThirdConsultation.R.R109Host
import NlsGge.ThirdConsultation.R.R110Host
import NlsGge.ThirdConsultation.PDE.BirkhoffRealization
import NlsGge.ThirdConsultation.PDE.OneSmoothing
import NlsGge.Atomic.R.R110
import NlsGge.Atomic.R.R115
import NlsGge.Atomic.I.I025

set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_densities_L1
    (lo up : ℝ) (c : BoundedCoefficients lo up)
    (s : ℝ) (hs : (1 : ℝ) / 2 < s) (hs' : s < 3 / 4) :
    (∀ N : ℕ, Integrable (fullFourierWeight c s N)
      (fullWeightedSequenceGaussian c s)) ∧
    Integrable (fullFourierDensity c s hs hs') (fullWeightedSequenceGaussian c s) ∧
    (∫ x, fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s) = ZW c ∧
    Tendsto (fun N : ℕ => eLpNorm
      (fun x : ECarrier38 c s => fullFourierWeight c s N x -
        fullFourierDensity c s hs hs' x) 1 (fullWeightedSequenceGaussian c s))
      atTop (𝓝 0) := by
  have hs1 : s ≤ 1 := by linarith
  have hW := NlsGge.ThirdConsultation.R.actual_fN_tendstoInMeasure c s hs hs'
  have hWpos : ∀ x : ECarrier38 c s, 0 <
      NlsGge.ThirdConsultation.R.actualRamerDensity c s hs hs1 x := by
    simpa [NlsGge.ThirdConsultation.R.actualRamerDensity,
      NlsGge.ThirdConsultation.R.weightedK] using
        (NlsGge.ThirdConsultation.R.actual_density_pushforward c s hs hs').1
  have hdens : fullFourierDensity c s hs hs' =
      NlsGge.ThirdConsultation.R.actualRamerDensity c s hs hs1 := by
    funext x
    simp [fullFourierDensity, NlsGge.ThirdConsultation.R.actualRamerDensity,
      NlsGge.ThirdConsultation.R.weightedK]
  have hNint : ∀ N : ℕ,
      Integrable (fullFourierWeight c s N) (fullWeightedSequenceGaussian c s) := by
    intro N
    exact NlsGge.Birkhoff.BirkhoffInput38.integrable_fN38 c hs N
  have hN0 : ∀ N : ℕ, ∀ x : ECarrier38 c s, 0 ≤ fullFourierWeight c s N x := by
    intro N x
    exact (NlsGge.Birkhoff.fN38_pos c s N x).le
  have hWint : Integrable (fullFourierDensity c s hs hs')
      (fullWeightedSequenceGaussian c s) := by
    rw [hdens]
    exact hW.1
  have hW0 : ∀ x : ECarrier38 c s, 0 ≤ fullFourierDensity c s hs hs' x := by
    intro x
    rw [hdens]
    exact (hWpos x).le
  have hWintegral :
      (∫ x, fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s) = ZW c := by
    calc
      (∫ x, fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s) =
          ∫ x, NlsGge.ThirdConsultation.R.actualRamerDensity c s hs hs1 x
            ∂fullWeightedSequenceGaussian c s := by rw [hdens]
      _ = PDE.actualBirkhoffInput38.ZW38 c.val := hW.2.1
      _ = ZW c := (NlsGge.ThirdConsultation.T.ZW_eq_actual lo up c).symm
  have hmeasure : TendstoInMeasure (fullWeightedSequenceGaussian c s)
      (fun N : ℕ => fullFourierWeight c s N) atTop
      (fullFourierDensity c s hs hs') := by
    simpa [fullFourierWeight, hdens] using hW.2.2
  have hmeanN : ∀ N : ℕ,
      (∫ x, fullFourierWeight c s N x ∂fullWeightedSequenceGaussian c s) =
        relativePartition c N := by
    intro N
    simpa [fullFourierWeight, relativePartition] using
      (NlsGge.Birkhoff.integral_fN38 c s hs N)
  have hmeanZW : Tendsto
      (fun N : ℕ => ∫ x, fullFourierWeight c s N x ∂fullWeightedSequenceGaussian c s)
      atTop (𝓝 (ZW c)) := by
    convert (NlsGge.ThirdConsultation.T.fullFourier_normalizers_limit_lower lo up c).2.1 using 1
    funext N
    exact hmeanN N
  have hmean : Tendsto
      (fun N : ℕ => ∫ x, fullFourierWeight c s N x ∂fullWeightedSequenceGaussian c s)
      atTop (𝓝 (∫ x, fullFourierDensity c s hs hs' x ∂fullWeightedSequenceGaussian c s)) := by
    rw [hWintegral]
    exact hmeanZW
  have hprob : IsProbabilityMeasure
      (show MeasureTheory.Measure (ECarrier38 c s) from
        NlsGge.Measure.fullWeightedSequenceGaussian c s) :=
    NlsGge.Measure.fullWeightedSequenceGaussian_probability c s
  have hL1 : Tendsto
      (fun N : ℕ => ∫ x, |fullFourierWeight c s N x - fullFourierDensity c s hs hs' x|
        ∂fullWeightedSequenceGaussian c s) atTop (𝓝 0) :=
    @NlsGge.Atomic.T.T013.T013_helper
      (ECarrier38 c s)
      (NlsGge.ThirdConsultation.T.eCarrierMeasurableSpace98 c s)
      (show MeasureTheory.Measure (ECarrier38 c s) from
        NlsGge.Measure.fullWeightedSequenceGaussian c s)
      hprob
      (fun N : ℕ => fullFourierWeight c s N)
      (fullFourierDensity c s hs hs')
      hN0 hW0 hNint hWint hmeasure hmean
  have hdiff : ∀ N : ℕ, Integrable
      (fun x : ECarrier38 c s => fullFourierWeight c s N x - fullFourierDensity c s hs hs' x)
      (fullWeightedSequenceGaussian c s) := by
    intro N
    exact (hNint N).sub hWint
  have hLpEq : ∀ N : ℕ,
      eLpNorm
          (fun x : ECarrier38 c s => fullFourierWeight c s N x - fullFourierDensity c s hs hs' x)
          1 (fullWeightedSequenceGaussian c s) =
        ENNReal.ofReal
          (∫ x, |fullFourierWeight c s N x - fullFourierDensity c s hs hs' x|
            ∂fullWeightedSequenceGaussian c s) := by
    intro N
    calc
      eLpNorm
          (fun x : ECarrier38 c s => fullFourierWeight c s N x - fullFourierDensity c s hs hs' x)
          1 (fullWeightedSequenceGaussian c s) =
        ∫⁻ x, ‖fullFourierWeight c s N x - fullFourierDensity c s hs hs' x‖ₑ
          ∂fullWeightedSequenceGaussian c s :=
            MeasureTheory.eLpNorm_one_eq_lintegral_enorm (hdiff N).aestronglyMeasurable
      _ = ENNReal.ofReal
          (∫ x, ‖fullFourierWeight c s N x - fullFourierDensity c s hs hs' x‖
            ∂fullWeightedSequenceGaussian c s) :=
            (MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hdiff N)).symm
      _ = ENNReal.ofReal
          (∫ x, |fullFourierWeight c s N x - fullFourierDensity c s hs hs' x|
            ∂fullWeightedSequenceGaussian c s) := by
            congr 1
  have hOfReal : Tendsto
      (fun N : ℕ => ENNReal.ofReal
        (∫ x, |fullFourierWeight c s N x - fullFourierDensity c s hs hs' x|
          ∂fullWeightedSequenceGaussian c s)) atTop (𝓝 0) := by
    have hcont : Tendsto ENNReal.ofReal (𝓝 (0 : ℝ)) (𝓝 (0 : ℝ≥0∞)) := by
      simpa using (ENNReal.continuous_ofReal.tendsto 0)
    convert hcont.comp hL1 using 1
    funext N
    rfl
  have hLp : Tendsto
      (fun N : ℕ => eLpNorm
        (fun x : ECarrier38 c s => fullFourierWeight c s N x -
          fullFourierDensity c s hs hs' x) 1 (fullWeightedSequenceGaussian c s))
      atTop (𝓝 0) := by
    rw [show (fun N : ℕ => eLpNorm
        (fun x : ECarrier38 c s => fullFourierWeight c s N x -
          fullFourierDensity c s hs hs' x) 1 (fullWeightedSequenceGaussian c s)) =
        (fun N : ℕ => ENNReal.ofReal
          (∫ x, |fullFourierWeight c s N x - fullFourierDensity c s hs hs' x|
            ∂fullWeightedSequenceGaussian c s)) from funext hLpEq]
    exact hOfReal
  exact ⟨hNint, hWint, hWintegral, hLp⟩

end
end NlsGge.ThirdConsultation.T
