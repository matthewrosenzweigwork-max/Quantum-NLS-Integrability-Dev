import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform5
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform9
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform10

/- KSPS025U11 PRODUCTION01 (proof development, AUTHOR; not self-reviewed, not accepted). GLUE (root main probe: joint
   closure above the worker-lane memory cap). Target NlsGge/ThirdConsultation/KSPS/KSPS025Uniform11.lean.
   Pro round-15 SUPPORT (never a packet), chain B. h24_of17: the h24 binder of KSPS025U7/U8 from the ball-uniform
   KSPS-017 critical tail h17U only; the three other inputs of KSPS025U10.h24_of17_of are discharged by the proved
   KSPSU1.crit_localization_uniform, KSPS025U5.riccati_consts_uniform, KSPS025U9.germ_uniform. -/
set_option autoImplicit false
open MeasureTheory Filter
open scoped BigOperators Topology

namespace NlsGge.ThirdConsultation.KSPS025U11
noncomputable section
open NlsGge.Pilot NlsGge.GK38
open NlsGge.ThirdConsultation.KSPS NlsGge.ThirdConsultation.KSPS021W NlsGge.ThirdConsultation.KSPS023W
open NlsGge.ThirdConsultation.KSPS024W

theorem h24_of17 (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀)
    (h17U : ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) *
          ‖deriv (discriminant φ) (criticalEigenvalue φ n) -
            NlsGge.ThirdConsultation.KSPSWKB.discriminantDerivativeMain N φ (criticalEigenvalue φ) n‖) ^ 2 ≤ C) :
    ∃ (M : ℕ) (C : ℝ), ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
      ∀ F : Finset ℤ, (∀ n ∈ F, (M : ℤ) ≤ |n|) →
        ∑ n ∈ F, (indexWeight n ^ (N + 1) * ‖criticalEigenvalue φ n - spectralPolynomial φ n‖) ^ 2 ≤ C :=
  NlsGge.ThirdConsultation.KSPS025U10.h24_of17_of N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPSU1.crit_localization_uniform N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPS025U5.riccati_consts_uniform N hN B₀ hB₀)
    (NlsGge.ThirdConsultation.KSPS025U9.germ_uniform N hN B₀ hB₀)
    h17U

end
end NlsGge.ThirdConsultation.KSPS025U11
