import Mathlib
import NlsGge.ThirdConsultation.I.LimitLaws
import NlsGge.Birkhoff.S04NlsInvariance38
import NlsGge.Birkhoff.H03Diagonal38b
import NlsGge.Spectral.SobolevToL2Map38
import NlsGge.Hierarchy.FiniteOrderGaussianTail38
import NlsGge.NLS38.PhysicalFlow38
import NlsGge.NLS38.FlowMaps38

                                                                                                                       
                                                                                                                       
                                                                                                          
                                                                                                       
                                                                                       
                                                                                                                             
                                                                                                                      
                                                                                                  
set_option autoImplicit false
noncomputable section
open MeasureTheory Filter
open scoped BigOperators ENNReal Topology ContDiff BoundedContinuousFunction
open NlsGge.Pilot NlsGge.Measure NlsGge.Weights
open NlsGge.SpectralFoundations
open NlsGge.Birkhoff NlsGge.Sobolev38 NlsGge.GKDefinitionDesign
open NlsGge.Atomic.I010 (spectralEnergy)
open NlsGge.ThirdConsultation

namespace NlsGge.ThirdConsultation.I
namespace I032Aux

theorem physFS_sobolevToL2 (m : ℕ) (y : SobolevHilbert (m : ℝ)) :
    physFS38 m (sobolevToL2_38 m y) = y := by
  apply coeffSeq38_injective
  funext n
  rw [coeffSeq_physFS38 m _ (sobolevToL2_38_sobolev m y) n, sobolevToL2_38_fourier]
  rfl

theorem reflC38_reflC38 (r : ℝ) (x : SobolevCarrier38 r) : reflC38 r (reflC38 r x) = x := by
  apply carrierExt38
  funext n
  simp

theorem physH_eq (m : ℕ) (v : PhysicalL2) : physH38 m v = reflC38 (m : ℝ) (toCarrier38 (m : ℝ) (physFS38 m v)) := by
  unfold physFS38
  rw [show toCarrier38 (m : ℝ) (ofCarrier38 (m : ℝ) (reflC38 (m : ℝ) (physH38 m v))) =
    reflC38 (m : ℝ) (physH38 m v) from rfl, reflC38_reflC38]

theorem i032_of (B : BirkhoffTop38) (lower upper : ℝ) (c : BoundedCoefficients lower upper)
    (hFl : BirkhoffNLSFlowInput38 B NlsGge.NLS38.nlsFlowL2)
    (hP : B.muW38 c.val = physicalLaw (weight c.val)) (t : ℝ) :
    (physicalLaw (weight c.val)).map (NlsGge.NLS38.nlsFlowL2 t) =
      physicalLaw (weight c.val) ∧
    ∀ m : ℕ, 1 ≤ m →
      Continuous (fun u : SobolevHilbert (m : ℝ) =>
        physFS38 m (NlsGge.NLS38.nlsFlowL2 t (sobolevToL2_38 m u))) ∧
      ∀ F : SobolevHilbert (m : ℝ) →ᵇ ℝ,
        (∫ u : PhysicalL2, F (physFS38 m (NlsGge.NLS38.nlsFlowL2 t u))
          ∂physicalLaw (weight c.val)) =
        ∫ u : PhysicalL2, F (physFS38 m u) ∂physicalLaw (weight c.val) := by
  obtain ⟨hlower, -, hc⟩ := c.property
  have hbound : ∀ j : ℕ, lower ≤ c.val j := fun j => (hc j).1
  have hupper : ∀ j : ℕ, c.val j ≤ upper := fun j => (hc j).2
  have hinv : (physicalLaw (weight c.val)).map (NlsGge.NLS38.nlsFlowL2 t) = physicalLaw (weight c.val) := by
    rw [← hP]
    exact BirkhoffTop38.S04_08_nlsFlow_invariant_muW B lower upper c.val hlower hbound hupper hFl t
  refine ⟨hinv, fun m hm => ⟨?_, fun F => ?_⟩⟩
  · have hfun : (fun u : SobolevHilbert (m : ℝ) =>
        physFS38 m (NlsGge.NLS38.nlsFlowL2 t (sobolevToL2_38 m u))) =
        fun u => ofCarrier38 (m : ℝ) (reflC38 (m : ℝ) (NlsGge.NLS38.nlsFlowC m hm t
          (reflC38 (m : ℝ) (toCarrier38 (m : ℝ) u)))) := by
      funext u
      have hmem : fourierSeq38 (sobolevToL2_38 m u) ∈ seqSobolev38 (m : ℝ) :=
        (fourierSeq38_mem_iff _ _).2 (sobolevToL2_38_sobolev m u)
      have h1 := NlsGge.NLS38.physH38_nlsFlowL2 m hm hmem t
      have h2 := physH_eq m (sobolevToL2_38 m u)
      rw [physFS_sobolevToL2] at h2
      show ofCarrier38 (m : ℝ) (reflC38 (m : ℝ) (physH38 m (NlsGge.NLS38.nlsFlowL2 t (sobolevToL2_38 m u)))) = _
      rw [h1, h2]
    rw [hfun]
    have hC : Continuous (NlsGge.NLS38.nlsFlowC m hm t) :=
      (NlsGge.NLS38.continuous_nlsFlowC_uncurry m hm).comp (continuous_const.prodMk continuous_id)
    exact (continuous_ofCarrier38 _).comp ((continuous_reflC38 _).comp (hC.comp
      ((continuous_reflC38 _).comp (continuous_toCarrier38 _))))
  · have hm' : AEStronglyMeasurable (fun v : PhysicalL2 => F (physFS38 m v))
        ((physicalLaw (weight c.val)).map (NlsGge.NLS38.nlsFlowL2 t)) :=
      (F.continuous.measurable.comp (measurable_physFS38 m)).aestronglyMeasurable
    rw [← integral_map (NlsGge.NLS38.measurable_nlsFlowL2 t).aemeasurable hm', hinv]

end I032Aux
end NlsGge.ThirdConsultation.I
