import Mathlib
import NlsGge.Atomic.M.M016ChartCore
import NlsGge.Atomic.M.M016RayCalib

                                                                                                       
                                                                                                                      
                                                                                                          
                                                                                                                
                                                                                                     
                                                                                                               
                                                                                                                 
                                                     

set_option autoImplicit false
open Set Filter Topology
open NlsGge.Pilot NlsGge.GK38

namespace NlsGge.ThirdConsultation.M

open NlsGge.ThirdConsultation.MPrimitive

theorem finitegap_pair_primitive_meromorphic_infinity_unfolded
    (φ : PotPair) (hW : φ ∈ gkW)
    (hfg : {n : ℤ | NlsGge.GKDefinitionDesign.gap φ n ≠ 0}.Finite) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      (0 < R ∧ ∀ z : ℂ, R < ‖z‖ →
        ∃ hz : φ ∈ gkW ∧ z ∈ endpointClosureFiber φ, F z = primitive ⟨(φ, z), hz⟩) ∧
      ExteriorHolomorphic F ∧
      AnalyticAtInfinity (fun z : ℂ => F z + Complex.I * z) ∧
      HasValueAtInfinity (fun z : ℂ => F z + Complex.I * z) 0 :=
  finitegap_pair_primitive_meromorphic_infinity_of_ray φ hW hfg (primitive_ray_calibration φ hW)

end NlsGge.ThirdConsultation.M
