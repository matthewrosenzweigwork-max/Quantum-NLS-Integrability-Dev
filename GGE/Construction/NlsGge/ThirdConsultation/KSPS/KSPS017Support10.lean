import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10
import NlsGge.ThirdConsultation.KSPS.KSPS012Support6

                                                                                                                      
                                                                                                                   
                                                                                                           
                                                                                         
                                                                                                    
                                                                                                              
                                                                                                                
                                                                   
set_option autoImplicit false
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPS017W
noncomputable section

theorem diag_strip (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (φ' : SobolevC 1)
    (hφ' : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ) (b : Bool) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ z : ℂ, ∀ hz : z ≠ 0, L ≤ ‖z‖ → |z.im| ≤ a →
      ‖KSPSWKB.sourceRemainderVector φ b ⟨z, hz⟩ 1 (if b then 1 else 0) -
        (-(sobolevPointValue 1 (if b then φ'.2 else φ'.1) 1) *
            ((2 * Complex.I * (((if b then -1 else 1 : ℤ) : ℂ) * z))⁻¹ *
              KSPSWKB.endpointOsc (((if b then -1 else 1 : ℤ) : ℂ) * z)
                (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))) +
          Complex.exp (-(Complex.I * (((if b then -1 else 1 : ℤ) : ℂ) * z))) *
            (2 * Complex.I * (((if b then -1 else 1 : ℤ) : ℂ) * z))⁻¹ *
            ((∫ t in (0 : ℝ)..1, coverRep38 (physicalSobolevEmbed 1 (if b then φ'.2 else φ'.1)) t *
                coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)) t) +
              NlsGge.ThirdConsultation.KSPS012Support5.Tz
                (coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ b (N + 1)))
                (coverRep38 (physicalSobolevDerivative38 1 (if b then φ'.2 else φ'.1)))
                (((if b then -1 else 1 : ℤ) : ℂ) * z)))‖ ≤ C / ‖z‖ ^ 2 := by
  cases b
  · obtain ⟨C, L, hC, hL, h⟩ := KSPSWKB.diag_approx_false hN φ φ' hφ' a ha
    refine ⟨C, L, hC, hL, fun z hz hzL him => ?_⟩
    have hcore := KSPSWKB.core_decomp φ'.1 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) hz
    have hb := h ⟨z, hz⟩ hzL him
    simp only [Bool.false_eq_true, ↓reduceIte, Int.cast_one, one_mul]
    rw [hcore] at hb
    refine le_of_eq_of_le ?_ hb
    congr 2
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring
  · obtain ⟨C, L, hC, hL, h⟩ := KSPSWKB.diag_approx_true hN φ φ' hφ' a ha
    refine ⟨C, L, hC, hL, fun z hz hzL him => ?_⟩
    have hz' : -z ≠ 0 := neg_ne_zero.2 hz
    have hcore := KSPSWKB.core_decomp φ'.2 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) hz'
    have hb := h ⟨z, hz⟩ hzL him
    simp only [↓reduceIte, Int.cast_neg, Int.cast_one, neg_one_mul]
    rw [hcore] at hb
    refine le_of_eq_of_le ?_ hb
    congr 2
    rw [div_eq_mul_inv, div_eq_mul_inv]; ring

end
end NlsGge.ThirdConsultation.KSPS017W
