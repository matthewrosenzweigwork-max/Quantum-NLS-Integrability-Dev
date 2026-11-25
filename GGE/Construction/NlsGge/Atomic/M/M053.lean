import Mathlib
import NlsGge.GK38.PairPotential
import NlsGge.ThirdConsultation.KSPSInversePhaseHost
import NlsGge.ThirdConsultation.M.M053Host
import NlsGge.ThirdConsultation.KSPSCoefficientHost
import NlsGge.ThirdConsultation.M.M053K1Support
import NlsGge.ThirdConsultation.M.M053Sup4

                                                          
                                                                          
                                                                                                              
                                                                                          
                                                                                
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.M
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.GKDefinitionDesign NlsGge.HierarchyRiccati.Core

theorem integralRiccatiCoefficient_eq_polyIntegral
    (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : ℕ) (hk2 : 2 ≤ k) (hkN : k ≤ N + 1) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ k =
      ∫ x in (0 : ℝ)..1,
        coverRep38 (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1 x *
        polynomialEvaluation (fun v => coverRep38 (hierarchyJetL2 φ v) x) (p k) := by
  have hN : 1 ≤ N := by omega
  unfold NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient
    NlsGge.ThirdConsultation.KSPS.integralRiccatiLeft
  rw [intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1),
    intervalIntegral.integral_of_le (by norm_num : (0:ℝ) ≤ 1)]
  refine integral_congr_ae (ae_restrict_of_ae ?_)
  filter_upwards [coverRep38_ae_phys (NlsGge.ThirdConsultation.KSPS.toPotPair φ).1,
    coverRep38_ae_phys (NlsGge.ThirdConsultation.KSPS.riccatiLeft φ k),
    left_cover_eq_polyEval hN φ k (by omega) hkN] with x h1 h2 h3
  have h3' : coverRep38 (NlsGge.ThirdConsultation.KSPS.riccatiLeft φ k) x =
      polynomialEvaluation (fun v => coverRep38 (hierarchyJetL2 φ v) x) (p k) := h3
  rw [← h1, ← h3', h2]

theorem WKB_hierarchy_coefficients_complex
    (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N + 1) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ k =
      if k = 1 then
        -NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge
          N φ ⟨k, hk, hkN⟩
      else
        NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge
          N φ ⟨k, hk, hkN⟩ := by
  by_cases hk1 : k = 1
  · subst hk1
    rw [if_pos rfl]
    exact WKB_hierarchy_coefficients_complex_one N φ hk hkN
  · rw [if_neg hk1, integralRiccatiCoefficient_eq_polyIntegral N φ k (by omega) hkN]
    unfold NlsGge.ThirdConsultation.MRiccati.sourceHierarchyCharge
    simp only [hk1, if_false]
    rfl

theorem WKB_hierarchy_coefficients
    (N : ℕ)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N)
    (hφ : NlsGge.ThirdConsultation.MRiccati.RealPair φ)
    (k : ℕ) (hk : 1 ≤ k) (hkN : k ≤ N + 1) :
    NlsGge.ThirdConsultation.KSPS.integralRiccatiCoefficient φ k =
      if k = 1 then
        -(massCharge
          (NlsGge.ThirdConsultation.MRiccati.realPhysicalFromPair φ) : ℂ)
      else
        hierarchyCharge φ ⟨k, hk, hkN⟩ := by
  by_cases hk1 : k = 1
  · subst hk1
    exact WKB_hierarchy_coefficients_one N φ hφ hk hkN
  · rw [if_neg hk1]
    have h := WKB_hierarchy_coefficients_complex N φ k hk hkN
    rw [if_neg hk1] at h
    exact h

end
end NlsGge.ThirdConsultation.M
