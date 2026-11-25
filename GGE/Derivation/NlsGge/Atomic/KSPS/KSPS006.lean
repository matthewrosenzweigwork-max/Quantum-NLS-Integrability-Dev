import Mathlib
import NlsGge.Atomic.KSPS.KSPS005
import NlsGge.ThirdConsultation.KSPS.KSPS006Host
import NlsGge.ThirdConsultation.KSPS.KSPS006Support

/- KSPS-006 PRODUCTION01 (proof development, AUTHOR; not reviewed; target NlsGge/Atomic/KSPS/KSPS006.lean).
   Head: Pro round 5 "Concrete repair of KSPS-006" (PRO_DEFINITION_RESPONSE_FP80_05.md ~line 1609; no round 6-11 text
   touches KSPS-006; STATEMENTS/KSPS.md still prints the refuted `inverse_fundamental_remainder`), VERBATIM: a joint
   estimate with ONE absolute constant C chosen before phi, x, lam, and the source factor `4 * C` for the inverse.
   Proof: C is the absolute constant of KSPS-005 (fundamental_two_term_remainder_uniform). The inverse remainder is the
   adjugate of the fundamental remainder (exact identity), and ||adjugate2 A|| <= 2||A|| <= 4||A||. -/
set_option autoImplicit false

open scoped Matrix.Norms.L2Operator

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem fundamental_and_inverse_two_term_remainder :
  ∃ C : ℝ, 0 < C ∧
    ∀ φ : SobolevC 1, ∀ x : ℝ, x ∈ Set.Icc (0 : ℝ) 1 →
      ∀ lam : ℂ, lam ≠ 0 →
        ‖fundamentalRemainder φ x lam‖ ≤
          C * fundamentalRemainderMajorant φ x lam ∧
        ‖inverseFundamentalRemainder φ x lam‖ ≤
          4 * C * fundamentalRemainderMajorant φ x lam := by
  obtain ⟨C, hC, h⟩ := fundamental_two_term_remainder_uniform
  refine ⟨C, hC, fun φ x hx lam hlam => ?_⟩
  have h1 := h φ x hx lam hlam
  have hmaj : C * Real.exp (|lam.im| * x + l2Norm φ) * sobolevNorm 1 φ ^ 2 *
      (1 + sobolevNorm 1 φ) / ‖lam‖ ^ 2 = C * fundamentalRemainderMajorant φ x lam := by
    unfold fundamentalRemainderMajorant
    ring
  rw [hmaj] at h1
  refine ⟨h1, ?_⟩
  rw [NlsGge.ThirdConsultation.KSPS006Support.inverseFundamentalRemainder_eq]
  have h2 := NlsGge.ThirdConsultation.KSPS006Support.norm_adjugate2_le_two (fundamentalRemainder φ x lam)
  have h0 := norm_nonneg (fundamentalRemainder φ x lam)
  nlinarith

end
end NlsGge.ThirdConsultation.KSPS
