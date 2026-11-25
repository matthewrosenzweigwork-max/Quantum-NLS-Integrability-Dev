import Mathlib
import NlsGge.Atomic.M.M016Step4
import NlsGge.Atomic.M.M016CutFreeConnected
import NlsGge.Atomic.M.M016BaseSign

                                                                                                         
                                                                                                                     
                                                                                                               
                                                                          
                                                                                                   
                                                                                           

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

theorem primitive_discriminant_identity_of_S4c (φ : PotPair) (hW : φ ∈ gkW)
    (hΔ : NlsGge.GK38.discrim φ (lamMinus φ 0) = 2)
    (z : ℂ) (hz : z ∈ MPrimitive.endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) = NlsGge.GK38.discrim φ z :=
  primitive_discriminant_identity_of_S4 φ hW (MPrimitive.cutFreeFiber_isPreconnected φ hW) hΔ z hz

theorem primitive_discriminant_identity
    (φ : PotPair) (hW : φ ∈ gkW) (z : ℂ)
    (hz : z ∈ MPrimitive.endpointClosureFiber φ) :
    2 * Complex.cosh (primitive ⟨(φ, z), ⟨hW, hz⟩⟩) =
      NlsGge.GK38.discrim φ z :=
  primitive_discriminant_identity_of_S4c φ hW (M016ChartAux.discrim_lamMinus_zero φ hW) z hz

end NlsGge.ThirdConsultation.M
