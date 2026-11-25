import Mathlib
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform4
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform6
import NlsGge.ThirdConsultation.KSPS.KSPS025Uniform7

                                                                                                                  
                                                                                                             
                                                                                                             
                                                                                                                     
                                                                                                                
                                                                                                                  
                                                                                                                
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
