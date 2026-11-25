import Mathlib
import NlsGge.Atomic.KSPS.KSPS006
import NlsGge.ThirdConsultation.KSPS.KSPS007Host
import NlsGge.ThirdConsultation.KSPS.KSPS007Support5
import NlsGge.ThirdConsultation.KSPS.KSPS007Support9
import NlsGge.ThirdConsultation.KSPS.KSPS007Support10

/- KSPS-007 PRODUCTION01 (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/KSPS/KSPS007.lean).
   Head: Pro round 5 "Concrete repair of KSPS-007 and all direct hosts" (PRO_DEFINITION_RESPONSE_FP80_05.md ~line 1630,
   followup9 copy), theorem `forced_solution_expansion`, VERBATIM (no round 6-11 text touches KSPS-007; the printed
   STATEMENTS/KSPS.md head, with a fixed F and lam bound after F, is superseded by Pro's repair).
   The absolute constants C, L depend only on LambdaIm, B (not on phi, f, lam, F, x), exactly as the head.
   Proof: variation of constants with the genuine inverse M^{-1} = adjugate2 M (det M = 1 from G1-010, SUPPORT01/04, NOT
   assumed); the first-order terms of M(x) M(t)^{-1} R cancel pointwise against the printed first correction
   (SUPPORT08 `theta_alg`, SUPPORT09 `remainder_eq_Ig`); what remains is bounded using KSPS-006 (absolute constant),
   the O(1/lam) bound of the first Volterra term (H1 integration by parts) and Cauchy-Schwarz int |f| <= ||f|| (SUPPORT10). -/
set_option autoImplicit false

open NlsGge.Pilot NlsGge.GK38
open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem forced_solution_expansion
    (LambdaIm B : ℝ) (hLambdaIm : 0 ≤ LambdaIm) (hB : 0 ≤ B) :
  ∃ C L : ℝ, 0 ≤ C ∧ 0 < L ∧
    ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B →
    ∀ f : PotPair, ∀ lam : ℂ, L ≤ ‖lam‖ → |lam.im| ≤ LambdaIm →
      ∀ F : ℝ → (Fin 2 → ℂ),
      NlsGge.ThirdConsultation.KSPSVolterra.ForcedZS φ lam f F →
      ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
        ‖F x -
          NlsGge.ThirdConsultation.KSPSVolterra.forcingLeading φ lam f x -
          NlsGge.ThirdConsultation.KSPSVolterra.forcingFirstCorrection φ lam f x‖ ≤
          C * NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f / ‖lam‖ ^ 2 := by
  obtain ⟨C6, hC6, h6⟩ := fundamental_and_inverse_two_term_remainder
  obtain ⟨K, hK0, hK⟩ := NlsGge.ThirdConsultation.KSPS007Support10.theta_pointwise LambdaIm B
    hLambdaIm hB C6 hC6.le (fun φ x hx lam hlam => h6 φ x hx lam hlam)
  refine ⟨2 * K, 1, by positivity, one_pos, ?_⟩
  intro φ hs f lam hL hΛ F hF x hx
  rw [NlsGge.ThirdConsultation.KSPS007Support9.remainder_eq_Ig φ lam f F hF hx]
  have h := NlsGge.ThirdConsultation.KSPS007Support5.Ig_norm_le f hx (b := K / ‖lam‖ ^ 2)
    (fun t ht => hK φ hs lam hL hΛ x hx t ht)
  calc _ ≤ 2 * (K / ‖lam‖ ^ 2) * Real.sqrt (‖f.1‖ ^ 2 + ‖f.2‖ ^ 2) := h
    _ = 2 * K * NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm f / ‖lam‖ ^ 2 := by
      unfold NlsGge.ThirdConsultation.KSPSVolterra.vectorL2Norm
      ring

end
end NlsGge.ThirdConsultation.KSPS
