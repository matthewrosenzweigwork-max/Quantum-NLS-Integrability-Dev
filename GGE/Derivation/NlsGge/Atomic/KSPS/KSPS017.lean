import Mathlib
import NlsGge.Atomic.KSPS.KSPS011
import NlsGge.Atomic.KSPS.KSPS012
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS017Host
import NlsGge.ThirdConsultation.KSPS.KSPS017Support3
import NlsGge.ThirdConsultation.KSPS.KSPS017Support6

/- KSPS-017 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS017.lean.
   Head: Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md Cluster 1 = followup12 STATEMENTS/KSPS.md,
   "KSPS-017 -- differentiated discriminant"), theorem `discriminant_derivative_WKB`, VERBATIM.
   Proof: KSPS017W.discriminant_derivative_WKB_of (Support3), whose hypotheses are discharged by the landed heads
   WKB_endpoint_offdiagonal (KSPS-011), WKB_endpoint_diagonal (KSPS-012), integrated_riccati_vanishing (KSPS-013),
   WKB_monodromy_entries (KSPS-014, B = sobolevNorm N φ), and by KSPS017W.h17d_holds / h17o_holds (Support6).
   No hypothesis added. NOT COMPILED IN THE WORKER LANE (memory cap): READY FOR ROOT MAIN PROBE. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem discriminant_derivative_WKB
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (xi : ℤ → ℂ)
    (hxi : ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    WeightedL2Error ((N + 1 : ℕ) : ℝ)
      (fun n : ℤ => deriv (discriminant φ) (xi n) -
        KSPSWKB.discriminantDerivativeMain N φ xi n) := by
  obtain ⟨a, ha, hxi'⟩ := hxi
  exact NlsGge.ThirdConsultation.KSPS017W.discriminant_derivative_WKB_of N hN φ xi a ha hxi'
    (WKB_endpoint_offdiagonal N hN φ xi ⟨a, ha, hxi'⟩)
    (WKB_endpoint_diagonal N hN φ xi ⟨a, ha, hxi'⟩)
    (fun k hk => integrated_riccati_vanishing N k φ hk)
    (fun lam hlam => (WKB_monodromy_entries N (sobolevNorm N φ) φ lam le_rfl hlam).2)
    (NlsGge.ThirdConsultation.KSPS017W.h17d_holds hN φ xi a ha hxi')
    (NlsGge.ThirdConsultation.KSPS017W.h17o_holds hN φ xi a ha hxi')

end
end NlsGge.ThirdConsultation.KSPS
