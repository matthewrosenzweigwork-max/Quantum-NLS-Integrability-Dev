import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS017Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform1
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform3
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform15
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform16

                                                                                                            
                                                                                                      
                                                                                                                  
                                                                                                
                                                                                                                 
                                                                                                                
                                                                                                            
                                                                                                                      
                                                                                                                
                                                                                                                
set_option autoImplicit false
open MeasureTheory
open scoped BigOperators

namespace NlsGge.ThirdConsultation.KSPS
noncomputable section
open NlsGge.Pilot NlsGge.GK38

theorem midpoint_spectral_expansion_uniform
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => midpoint φ n - spectralPolynomial φ n) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖midpoint φ n - spectralPolynomial φ n‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U15.midpoint_spectral_expansion_uniform_of24 N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPS017U6.h24_uniform N hN B₀ hB₀)

theorem midpoint_first_order_uniform
    (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ B : ℝ, 0 < B ∧
      ∀ φ : SobolevC 1, sobolevNorm 1 φ ≤ B₀ →
        ‖massCoefficient φ‖ ≤ B ∧
        ∀ k : ℤ, k ≠ 0 →
          ‖midpoint φ k - (k : ℂ) * Real.pi -
            massCoefficient φ / (k : ℂ)‖ ≤
              B / (k.natAbs : ℝ)^2 :=
  NlsGge.ThirdConsultation.KSPS025U3.midpoint_first_order_uniform_of
    NlsGge.ThirdConsultation.KSPS.midpoint_spectral_expansion_uniform
    NlsGge.ThirdConsultation.KSPS.first_two_spectral_coefficients_bounded B₀ hB₀

theorem midpoint_dirichlet_difference_uniform
    (N : ℕ) (hN : 1 ≤ N) (B₀ : ℝ) (hB₀ : 0 ≤ B₀) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ φ : SobolevC N, sobolevNorm N φ ≤ B₀ →
        WeightedL2Error ((N + 1 : ℕ) : ℝ)
          (fun n => midpoint φ n - mu φ n +
            (physicalFourier (toPotPair φ).1 (-n) +
             physicalFourier (toPotPair φ).2 n) / 2) ∧
        ∀ F : Finset ℤ,
          (∑ n ∈ F,
            (indexWeight n ^ (N + 1) *
              ‖midpoint φ n - mu φ n +
                (physicalFourier (toPotPair φ).1 (-n) +
                 physicalFourier (toPotPair φ).2 n) / 2‖)^2) ≤ C^2 :=
  NlsGge.ThirdConsultation.KSPS025U16.midpoint_dirichlet_difference_uniform_of24 N hN B₀ hB₀
    (NlsGge.ThirdConsultation.KSPS017U6.h24_uniform N hN B₀ hB₀)

end
end NlsGge.ThirdConsultation.KSPS
