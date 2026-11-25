import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS012Support11

/- KSPS-012 PRODUCTION01 (proof development, AUTHOR; not reviewed). Target NlsGge/Atomic/KSPS/KSPS012.lean.
   Head: Pro round 14 (PRO_DEFINITION_RESPONSE_FP80_14.md, Cluster 1, "KSPS-012 -- diagonal endpoint remainders"),
   theorem `WKB_endpoint_diagonal`, VERBATIM up to lexical qualification of the KSPSWKB names. eLower/eUpper are
   indexWeight n * (endpoint - leading term) for ALL n, so the identity is algebra and the content is
   SquareSummable (KSPS012Support11.diag_lower_sq_summable / diag_upper_sq_summable). -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section

theorem WKB_endpoint_diagonal
    (N : ℕ) (hN : 1 ≤ N) (φ : SobolevC N)
    (xi : ℤ → ℂ)
    (hxi : ∃ a : ℝ, 0 ≤ a ∧ ∀ n : ℤ,
      ‖xi n - (n : ℂ) * (Real.pi : ℂ)‖ ≤ a / indexWeight n) :
    ∃ e1 e2 : ℤ → ℂ,
      SquareSummable e1 ∧ SquareSummable e2 ∧
      ∀ n : ℤ,
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n =
          (-1 : ℂ) ^ n / (2 * Complex.I * xi n) *
            integralRiccatiLeft φ (N + 1) +
          e1 n / (indexValue n : ℂ) ∧
        NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n =
          (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) *
            integralRiccatiRight φ (N + 1) +
          e2 n / (indexValue n : ℂ) := by
  obtain ⟨a, ha, hxi'⟩ := hxi
  have hL := NlsGge.ThirdConsultation.KSPSWKB.diag_lower_sq_summable hN φ a ha xi hxi'
  have hU := NlsGge.ThirdConsultation.KSPSWKB.diag_upper_sq_summable hN φ a ha xi hxi'
  have hw : ∀ n : ℤ, (indexWeight n : ℂ) ≠ 0 := fun n => by
    exact_mod_cast (indexWeight_pos n).ne'
  refine ⟨fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalLower N φ xi n -
        (-1 : ℂ) ^ n / (2 * Complex.I * xi n) * integralRiccatiLeft φ (N + 1)),
    fun n => (indexWeight n : ℂ) *
      (NlsGge.ThirdConsultation.KSPSWKB.endpointDiagonalUpper N φ xi n -
        (-1 : ℂ) ^ (n + 1) / (2 * Complex.I * xi n) * integralRiccatiRight φ (N + 1)),
    hL, hU, fun n => ⟨?_, ?_⟩⟩
  · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
    rw [mul_div_cancel_left₀ _ (hw n)]
    ring
  · show _ = _ + (indexWeight n : ℂ) * _ / (indexWeight n : ℂ)
    rw [mul_div_cancel_left₀ _ (hw n)]
    ring

end
end NlsGge.ThirdConsultation.KSPS
