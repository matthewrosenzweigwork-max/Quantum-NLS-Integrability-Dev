import Mathlib
import NlsGge.Atomic.M.M048
import NlsGge.Atomic.M.M049Of
import NlsGge.ThirdConsultation.PDE.BirkhoffInversePoly

                                                                                                  
                                                                                                             
                                                                                                                      
                                                                                                     
                                                                                                                      
                                                              
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem molnar_inverse_birkhoff (m : ℕ) (hm : 1 ≤ m) :
    ∃ D : ℝ, 0 < D ∧ ∀ z : RealSobolevSequence m,
      ‖birkhoffInverse m z‖ ≤
        D * (‖z‖ +
          (1 + ‖NlsGge.Birkhoff.carrierIncl38
            (r := 1) (s := (m : ℝ)) (by exact_mod_cast hm) z‖) ^ (4 * m - 3) *
            ‖NlsGge.Birkhoff.carrierIncl38
              (r := 0) (s := (m : ℝ)) (by positivity) z‖) :=
  molnar_inverse_birkhoff_of_actions m hm (molnar_inverse_actions m hm)

/-- Exact quantitative ABI for the concrete Molnar field; no arbitrary B. -/
theorem actual_inverse_polynomial_for_birkhoff_input
    (m : ℕ) (hm : 1 ≤ m) :
    ∃ C : ℝ, ∃ d : ℕ,
      ∀ z : NlsGge.Sobolev38.SobolevCarrier38 (m : ℝ),
        ‖NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38.TinvC m z‖ ≤
          C * (1 + ‖z‖) ^ d := by
  obtain ⟨C, -, hC⟩ :=
    NlsGge.ThirdConsultation.PDE.actualBirkhoffTop38_inverse_polynomial_of m hm (molnar_inverse_birkhoff m hm)
  exact ⟨C, 4 * m - 2, hC⟩

end NlsGge.ThirdConsultation.M
