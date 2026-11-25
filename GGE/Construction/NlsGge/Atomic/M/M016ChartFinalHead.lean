import Mathlib
import NlsGge.Atomic.M.M016ChartFinal
import NlsGge.Atomic.M.M052
import NlsGge.ThirdConsultation.M.FiniteGapPair

                                                                                                                                                   
                                                                                                 
                                                                     
                                                                                                     
                                                                                                         
                                                                                 
set_option autoImplicit false
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem finitegap_pair_primitive_meromorphic_infinity
    (φ : PotPair) (hW : φ ∈ gkW) (hfg : finiteGapPair φ) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative φ R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      MPrimitive.HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 :=
  finitegap_pair_primitive_meromorphic_infinity_unfolded φ hW hfg

end NlsGge.ThirdConsultation.M
