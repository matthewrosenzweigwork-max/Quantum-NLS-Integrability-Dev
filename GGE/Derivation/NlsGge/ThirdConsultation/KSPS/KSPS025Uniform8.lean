import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform4
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform7

/- KSPS025U8 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe: the joint
   closure exceeds the worker-lane memory cap; KSPS025U7_SELFTEST01 RUN01 fa542bfb exit -6 memory_exception).
   Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform8.lean. Pro round-15 SUPPORT (never a packet), chain B.
   midpoint_spectral_expansion_uniform_of26_24: Pro's Q2 `midpoint_spectral_expansion_uniform` conclusion at (N, B₀),
   CONDITIONAL only on the two ball-uniform tail hypotheses h26 (uniform KSPS-026) and h24 (uniform KSPS-024) of
   KSPS025U7.midpoint_spectral_expansion_uniform_of; the three other hypotheses of that core are discharged by the
   proved supports KSPS025U4.periodic_loc_uniform, KSPS025U4.g1054_ball, KSPS025U6.spectralPolynomial_sub_le. -/
set_option autoImplicit false

namespace NlsGge.ThirdConsultation.KSPS025U8
noncomputable section
open NlsGge.Pilot NlsGge.GK38 NlsGge.ThirdConsultation.KSPS

theorem midpoint_spectral_expansion_uniform_of26_24
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (h26 : ∃ (M : ℕ) (CE : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      (∀ (upper : Bool) (i j : Fin 2) (F : Finset ℤ), (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖KSPSWKB.endpointEntryError N φ upper i j n‖) ^ 2 ≤ CE) ∧
      ∃ hplus hminus : ℤ → ℂ, ∀ n : ℤ, (M : ℤ) ≤ |n| →
        KSPSWKB.endpointQuadraticFormula N φ n hplus hminus)
    (h24 : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖NlsGge.ThirdConsultation.KSPS.midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U7.midpoint_spectral_expansion_uniform_of N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPS025U4.periodic_loc_uniform N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPS025U4.g1054_ball N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPS025U6.spectralPolynomial_sub_le N hN B₀ hB₀)
    h26 h24

end
end NlsGge.ThirdConsultation.KSPS025U8
