import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPSUniformU1
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform5
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform9
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform10

                                                                                                               
                                                                                                         
                                                                                                                 
                                                                                                                  
                                                                                                 
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
