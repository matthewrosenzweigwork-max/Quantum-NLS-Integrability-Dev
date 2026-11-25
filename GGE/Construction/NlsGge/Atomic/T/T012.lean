import Mathlib
import NlsGge.Definitions.BorelWeighted
import NlsGge.Birkhoff.W04WeightedSmoothing38
import NlsGge.Birkhoff.W05FiniteGap38
import NlsGge.Birkhoff.W07Probability38
import NlsGge.Birkhoff.W09Approx38
import NlsGge.Birkhoff.W09Approx38b
import NlsGge.Birkhoff.F09Limit38
import NlsGge.Measure.CountableReconstruction
import NlsGge.Hierarchy.RelativePartition38
import NlsGge.Weights.Entire
import NlsGge.Birkhoff.F09Limit38b
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.ThirdConsultation.Common.FiniteSupport
import NlsGge.ThirdConsultation.T.ECarrier98
import NlsGge.ThirdConsultation.T.TDefs2Host
import NlsGge.Atomic.T.T005
import NlsGge.Atomic.T.T009
import NlsGge.Atomic.T.T012Sup

                                                         
                                                                                
                                                                           
set_option autoImplicit false
open Set Filter MeasureTheory
open scoped ENNReal Topology BigOperators ContDiff
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights NlsGge.Sobolev38
open NlsGge.Birkhoff NlsGge.HierarchyRiccati.Core
open NlsGge.ThirdConsultation.Common

namespace NlsGge.ThirdConsultation.T
noncomputable section

theorem fullFourier_uniform_expH2
    (lo up : ℝ) (hlo : 0 < lo) (hup : lo ≤ up) :
    ∃ eta : ℝ, 0 < eta ∧
      ∀ c : BoundedCoefficients lo up, ∃ C : ℝ, 0 < C ∧
        ∀ N : ℕ,
          Integrable (fun u : PhysicalL2 => Real.exp (eta * ‖physFS38 2 u‖ ^ 2))
            (fullFourierLaw c N) ∧
          (∫ u : PhysicalL2, Real.exp (eta * ‖physFS38 2 u‖ ^ 2)
            ∂fullFourierLaw c N) ≤ C := by
  obtain ⟨eta, C0, heta, hC0, hmom⟩ :=
    fullFourier_unnormalized_expH2 lo up hlo hup
  refine ⟨eta, heta, fun c => ?_⟩
  obtain ⟨_, _, ⟨zmin, hzmin, hzN⟩⟩ := fullFourier_normalizers_limit_lower lo up c
  refine ⟨C0 / zmin, div_pos hC0 hzmin, fun N => ?_⟩
  let s : ℝ := 5 / 8
  have hs : (1 : ℝ) / 2 < s := by dsimp only [s]; norm_num
  have hnumData := hmom c s hs N
  have hden := T012Sup.expH2_withDensity_ECarrier98 c s N eta hnumData.1
  have hI := T012Sup.expH2_integrable_nuWN38_of_ECarrier98 c s hs N eta hden.1
  have hnum := T012Sup.expH2_numerator_bound_FullWeighted_of_ECarrier98
    c s N eta C0 hnumData.2
  have hzN38 : zmin ≤ relativePartition38 c N := by
    have h := hzN N
    unfold relativePartition at h
    exact h
  have hinv : 1 / relativePartition38 c N ≤ 1 / zmin :=
    one_div_le_one_div_of_le hzmin hzN38
  let G : PhysicalL2 → ℝ := fun u => Real.exp (eta * ‖physFS38 2 u‖ ^ 2)
  have hG : Measurable G :=
    Real.measurable_exp.comp (((measurable_physFS38 2).norm.pow_const 2).const_mul eta)
  have hplane : Measurable (fun z : FourierPlane N => G (planeL2 N z)) :=
    hG.comp (measurableEmbedding_planeL2_38 N).measurable
  have hbridge := integral_nuWN38_Es c s hs N G hplane
  let A : ℝ := ∫ x : FullWeightedHilbert c s,
    G (physOfE38 c s (projE38 c s N x)) * fN38 c s N x
      ∂fullWeightedSequenceGaussian c s
  have hA0 : 0 ≤ A := hnum.1
  have hAC : A ≤ C0 := hnum.2
  refine ⟨?_, ?_⟩
  · change Integrable (fun u : PhysicalL2 => Real.exp (eta * ‖physFS38 2 u‖ ^ 2))
      (nuWN38 c N)
    exact hI
  · change (∫ u : PhysicalL2, G u ∂nuWN38 c N) ≤ C0 / zmin
    calc
      _ = (1 / relativePartition38 c N) * A := hbridge
      _ ≤ (1 / zmin) * A := mul_le_mul_of_nonneg_right hinv hA0
      _ ≤ (1 / zmin) * C0 := mul_le_mul_of_nonneg_left hAC (one_div_pos.2 hzmin).le
      _ = C0 / zmin := by ring

end
end NlsGge.ThirdConsultation.T
