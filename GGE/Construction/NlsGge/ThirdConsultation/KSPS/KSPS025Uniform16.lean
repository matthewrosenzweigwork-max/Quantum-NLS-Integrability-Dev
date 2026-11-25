import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform15
import NlsGge.ThirdConsultation.KSPS.KSPS023Uniform2

                                                                                                          
                                                                                                              
                                                                                                                        
                                                                                                                
                                                                                                  
                                                                              
                                                                                                             
                                                                                                         
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
