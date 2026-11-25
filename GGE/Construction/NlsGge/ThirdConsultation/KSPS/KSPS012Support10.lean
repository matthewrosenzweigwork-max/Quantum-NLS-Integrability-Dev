import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support4
import NlsGge.ThirdConsultation.KSPS.KSPS012Support9
import NlsGge.ThirdConsultation.KSPS.KSPS011Support8
import NlsGge.ThirdConsultation.KSPS.KSPS011Support5
import NlsGge.ThirdConsultation.KSPS.KSPS011Support6
import NlsGge.ThirdConsultation.KSPS.KSPS011Support4

                                                                                                                      
                                                                                      
                                                                                                                     
                                                                                                         
                                                       
set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff NlsGge.Atomic.Common NlsGge.GK38
open NlsGge.Schur NlsGge.Analysis NlsGge.GKDefinitionDesign NlsGge.ThirdConsultation.KSPS

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem forcing_intervalIntegrable {N : ℕ} (φ : SobolevC N) (b : Bool) (lam : ℂ) :
    IntervalIntegrable (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ b lam) volume 0 1 := by
  have h := NlsGge.ThirdConsultation.KSPSSupport.h150_forcing_memLp φ b lam
  exact intervalIntegrable_of_memLp h

theorem diag_approx_false {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (φ' : SobolevC 1)
    (hφ' : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ false lam 1 0 -
        (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := sourceRemainder_endpoint_expansion hN φ φ' hφ' a ha
  obtain ⟨C1, hC1, hF⟩ := F_to_c_bound hN φ false φ'.1 a ha L8 hL8
  refine ⟨C8 + C1, max L8 1, by positivity, le_max_right _ _, fun lam hL him => ?_⟩
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  obtain ⟨f, hf⟩ := exists_forcing_potPair φ false lam
  have hv := h8 false lam hL8' him f hf
  have hU : ‖sourceRemainderVector φ false lam 1 0 -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have : (sourceRemainderVector φ false lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 =
        sourceRemainderVector φ false lam 1 0 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← this]
    exact norm_le_pi_norm _ _
  have hcomp := lower_diag_component φ' lam.1 lam.2 f
    (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ false lam.1)
    (forcing_intervalIntegrable φ false lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
  have hX := hF lam.1 lam.1 hl1 hL8' rfl him
  have hXF : ‖(NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))‖ ≤
      C1 / ‖lam.1‖ ^ 2 := by
    rw [hcomp]
    exact hX
  have e : sourceRemainderVector φ false lam 1 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t)) =
      (sourceRemainderVector φ false lam 1 0 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0) +
      ((NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 0 -
      (-Complex.exp (-(2 * Complex.I * lam.1)) * endpointOsc lam.1 (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * lam.1 * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.1) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ false (N + 1)) t))) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ C8 / ‖lam.1‖ ^ 2 + C1 / ‖lam.1‖ ^ 2 := add_le_add hU hXF
    _ = (C8 + C1) / ‖lam.1‖ ^ 2 := by ring

theorem diag_approx_true {N : ℕ} (hN : 1 ≤ N) (φ : SobolevC N) (φ' : SobolevC 1)
    (hφ' : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = toPotPair φ) (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 1 ≤ L ∧ ∀ lam : {z : ℂ // z ≠ 0}, L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ‖sourceRemainderVector φ true lam 1 1 -
        (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
        C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C8, L8, hC8, hL8, h8⟩ := sourceRemainder_endpoint_expansion hN φ φ' hφ' a ha
  obtain ⟨C1, hC1, hF⟩ := F_to_c_bound hN φ true φ'.2 a ha L8 hL8
  refine ⟨C8 + C1, max L8 1, by positivity, le_max_right _ _, fun lam hL him => ?_⟩
  have hL8' : L8 ≤ ‖lam.1‖ := (le_max_left _ _).trans hL
  have hl1 : 1 ≤ ‖lam.1‖ := (le_max_right _ _).trans hL
  obtain ⟨f, hf⟩ := exists_forcing_potPair φ true lam
  have hv := h8 true lam hL8' him f hf
  have hU : ‖sourceRemainderVector φ true lam 1 1 -
      (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1‖ ≤
      C8 / ‖lam.1‖ ^ 2 := by
    refine le_trans ?_ hv
    have : (sourceRemainderVector φ true lam 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 =
        sourceRemainderVector φ true lam 1 1 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 := by
      simp only [Pi.sub_apply, Pi.add_apply, sub_sub]
    rw [← this]
    exact norm_le_pi_norm _ _
  have hcomp := upper_diag_component φ' lam.1 lam.2 f
    (NlsGge.ThirdConsultation.KSPSRiccati.forcing φ true lam.1)
    (forcing_intervalIntegrable φ true lam.1) (by
      refine hf.mono (fun t ht => ?_)
      rw [ht]
      simp [sourceForcingVector])
  have him' : |(-lam.1).im| ≤ a := by simpa using him
  have hX := hF lam.1 (-lam.1) hl1 hL8' (norm_neg _) him'
  have hXF : ‖(NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))‖ ≤
      C1 / ‖lam.1‖ ^ 2 := by
    rw [hcomp]
    exact hX
  have e : sourceRemainderVector φ true lam 1 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t)) =
      (sourceRemainderVector φ true lam 1 1 -
        (NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1) +
      ((NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 +
        NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1) 1 -
      (-Complex.exp (-(2 * Complex.I * (-lam.1))) * endpointOsc (-lam.1) (fun t =>
          (∫ s in t..1, Complex.exp (2 * Complex.I * (-lam.1) * (s : ℂ)) *
            coverRep38 (physicalSobolevEmbed 1 φ'.2) s) *
          coverRep38 (NlsGge.ThirdConsultation.KSPSRiccati.coefficient φ true (N + 1)) t))) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  calc _ ≤ C8 / ‖lam.1‖ ^ 2 + C1 / ‖lam.1‖ ^ 2 := add_le_add hU hXF
    _ = (C8 + C1) / ‖lam.1‖ ^ 2 := by ring

end NlsGge.ThirdConsultation.KSPSWKB
