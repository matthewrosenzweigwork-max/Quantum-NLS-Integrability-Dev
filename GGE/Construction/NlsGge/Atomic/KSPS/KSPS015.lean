import Mathlib
import NlsGge.Atomic.KSPS.KSPS011
import NlsGge.Atomic.KSPS.KSPS012
import NlsGge.Atomic.KSPS.KSPS013
import NlsGge.Atomic.KSPS.KSPS014
import NlsGge.ThirdConsultation.KSPS.KSPS015Support

                                                                                                     
                                                                                                                 
                                                                                   
                                                                                                                
                                                                                                                   
                                                                                                     
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
