import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS011Support6
import NlsGge.ThirdConsultation.KSPS.KSPS011Support7
import NlsGge.Atomic.KSPS.KSPS007

/- KSPS-011 SUPPORT8 (proof development, AUTHOR; not reviewed). Target NlsGge/ThirdConsultation/KSPS/KSPS011Support8.lean.
   Step M3b: for phi : SobolevC N (N >= 1), phi' : SobolevC 1 with toPair phi' = toPotPair phi, there are C, L with
   |sourceRemainderVector phi b lam 1 - forcingLeading phi' lam f 1 - forcingFirstCorrection phi' lam f 1| <= C/|lam|^2
   for |lam| >= L, |Im lam| <= a, and EVERY PotPair f representing the source forcing a.e. on [0,1].
   Route: KSPS-007 forced_solution_expansion with B := sobolevNorm 1 phi' (Support6 ForcedZS) and Support7 (M3a) with Lambda := L. -/
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.KSPSWKB

theorem sourceRemainder_endpoint_expansion {N : ℕ} (hN : 1 ≤ N)
    (φ : NlsGge.ThirdConsultation.KSPS.SobolevC N) (φ' : NlsGge.ThirdConsultation.KSPS.SobolevC 1)
    (hφ : NlsGge.ThirdConsultation.KSPSVolterra.toPair φ' = NlsGge.ThirdConsultation.KSPS.toPotPair φ)
    (a : ℝ) (ha : 0 ≤ a) :
    ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧ ∀ (b : Bool) (lam : {z : ℂ // z ≠ 0}), L ≤ ‖lam.1‖ → |lam.1.im| ≤ a →
      ∀ f : PotPair,
        (∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) 1)),
          ![potRepFst38 f t, potRepSnd38 f t] = sourceForcingVector φ b lam t) →
        ‖sourceRemainderVector φ b lam 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ' lam.1 f 1 -
            NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ' lam.1 f 1‖ ≤
          C / ‖lam.1‖ ^ 2 := by
  obtain ⟨C0, L, hC0, hL, h7⟩ := NlsGge.ThirdConsultation.KSPS.forced_solution_expansion a
    (NlsGge.ThirdConsultation.KSPS.sobolevNorm 1 φ') ha (Real.sqrt_nonneg _)
  obtain ⟨K, hK0, hK⟩ := sourceForcing_vectorL2Norm_le hN φ L a hL ha
  refine ⟨C0 * K, L, by positivity, hL, fun b lam hlam hIm f hf => ?_⟩
  have hF := sourceRemainderVector_forcedZS φ φ' hφ b lam f hf
  have h := h7 φ' le_rfl f lam.1 hlam hIm _ hF 1 ⟨zero_le_one, le_rfl⟩
  refine h.trans ?_
  rw [mul_div_assoc, mul_div_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hC0
  exact div_le_div_of_nonneg_right (hK b lam hlam hIm f hf) (by positivity)

end NlsGge.ThirdConsultation.KSPSWKB
