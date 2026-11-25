import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform15
import NlsGge.ThirdConsultation.KSPS.KSPS023Uniform2

/- KSPS025U16 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform16.lean. Pro round-15 SUPPORT (never a packet), chain B.
   midpoint_dirichlet_difference_uniform_of24: the conclusion of Pro r15 Q5 `KSPS.midpoint_dirichlet_difference_uniform`
   (lines ~814-830 of PRO_DEFINITION_RESPONSE_FP80_15.md), CONDITIONAL ONLY on h24 (the uniform KSPS-024 tail of
   KSPS025U7/U8; reduced by proof development's KSPS025U10/U11 to h17U, which proof development is producing):
   KSPS023U.midpoint_dirichlet_difference_of (weighted-l2 triangle) applied to
   KSPS025U15.midpoint_spectral_expansion_uniform_of24 h24 and KSPS023U.dirichlet_spectral_expansion_uniform.
   This is NOT Pro's head (which has no h24); once h24 is a theorem, Pro's head is this applied to it. -/
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS025U16
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

theorem midpoint_dirichlet_difference_uniform_of24
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (h24 : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
            (physicalFourier (toPotPair φ).1 (-n) +
             physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - mu φ n +
                (physicalFourier (toPotPair φ).1 (-n) +
                 physicalFourier (toPotPair φ).2 n) / 2‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS023U.midpoint_dirichlet_difference_of N B₀
    (NlsGge.ThirdConsultation.KSPS025U15.midpoint_spectral_expansion_uniform_of24 N hN B₀ hB₀ h24)
    (NlsGge.ThirdConsultation.KSPS023U.dirichlet_spectral_expansion_uniform N hN B₀ hB₀)

end
end NlsGge.ThirdConsultation.KSPS025U16
