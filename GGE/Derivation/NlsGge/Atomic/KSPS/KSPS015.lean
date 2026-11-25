import Mathlib
import NlsGge.Atomic.KSPS.KSPS011
import NlsGge.Atomic.KSPS.KSPS012
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS015Support

/- KSPS-015 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS015.lean.
   Head: Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md, Cluster 1, "KSPS-015 -- discriminant WKB cancellation"
   = followup12 STATEMENTS/KSPS.md), theorem `discriminant_WKB_sequence`, VERBATIM.
   Proof: KSPS015Support.discriminant_WKB_sequence_of, whose four explicit hypotheses are discharged here by the
   landed heads WKB_endpoint_offdiagonal (KSPS-011), WKB_endpoint_diagonal (KSPS-012), integrated_riccati_vanishing
   (KSPS-013) and WKB_monodromy_entries (KSPS-014, with B = sobolevNorm N φ). No hypothesis added. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem discriminant_WKB_sequence
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N) (xi : ℤ → ℂ)
    (hxi : ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => discriminant φ (xi n) -
        2 * Complex.cos (wkbPhase φ (xi n))) := by
  obtain ⟨a, ha, hxi'⟩ := hxi
  exact NlsGge.ThirdConsultation.KSPS015W.discriminant_WKB_sequence_of N hN φ xi a ha hxi'
    (WKB_endpoint_offdiagonal N hN φ xi ⟨a, ha, hxi'⟩)
    (WKB_endpoint_diagonal N hN φ xi ⟨a, ha, hxi'⟩)
    (fun k hk => integrated_riccati_vanishing N k φ hk)
    (fun lam hlam => (WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2)

end
end NlsGge.ThirdConsultation.KSPS
