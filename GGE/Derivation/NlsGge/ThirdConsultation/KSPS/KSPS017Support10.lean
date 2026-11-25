import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support10
import NlsGge.ThirdConsultation.KSPS.KSPS012Support6

/- KSPS-017 SUPPORT10 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS017Support10.lean.
   UNIFORM strip approximation of the DIAGONAL endpoint remainders by the explicit principal part (the product form
   of the right side of KSPS012Support6.core_decomp; it is definitionally KSPS017W.Pdiag sigma c d u1 J z):
   |R_b(z,1)_{idx_b} - Pdiag(z)| <= C/|z|^2 for |z| >= L, |Im z| <= a, every z != 0, with
   (sigma, u) = (1, phi'.1) for b = false (component 0) and (-1, phi'.2) for b = true (component 1),
   c = top Riccati coefficient, d = u', u1 = u(1), J = int u c. Route: KSPS012Support10 diag_approx_false/true
   (KSPS-007 forced expansion) and the exact identity core_decomp at mu = sigma z. (Kept free of KSPS017Support8
   so that the worker selftest stays under the lane memory cap.) -/
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
