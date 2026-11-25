import Mathlib
import NlsGge.Atomic.M.M052
import NlsGge.Atomic.M.M053
import NlsGge.Atomic.KSPS.KSPS031
import NlsGge.Atomic.M.M016Coeff
import NlsGge.Atomic.M.M016Laurent

                                                                                                                 
                                                                                                       
                                                                                                                    
                                                                                                                         
                                     
                                                                                                                           
                                                                                                        
                                                                                                                       
                                                                                                                      
                                                                                    
set_option autoImplicit false
open Set Filter Topology Metric
open NlsGge.Pilot NlsGge.GK38 NlsGge.SpectralFoundations
open NlsGge.GKDefinitionDesign

namespace NlsGge.ThirdConsultation.M

theorem finitegap_primitive_laurent_real
    (u : PhysicalL2) (hfg : finiteGap u)
    (hsmooth : ∀ N : ℕ, ∃ φ : KSPS.SobolevC N,
      KSPS.toPotPair φ = realSlice u) :
    ∃ R : ℝ, ∃ F : ℂ → ℂ,
      ExteriorPrimitiveRepresentative (realSlice u) R F ∧
      MPrimitive.ExteriorHolomorphic F ∧
      ∀ N : ℕ, ∀ φ : KSPS.SobolevC N,
        KSPS.toPotPair φ = realSlice u → PrimitiveLaurentCoefficients N φ F := by
  obtain ⟨R, F, hrep, hhol, hG, hval⟩ := finitegap_primitive_meromorphic_infinity u hfg
  refine ⟨R, F, hrep, hhol, fun N φ hφ => ?_⟩
  obtain ⟨ψ, hψ⟩ := hsmooth (N + 2)
  obtain ⟨C, J, hC, h031⟩ := NlsGge.ThirdConsultation.KSPS.nonresonant_WKB_coefficients (N + 2) (by omega) ψ
  exact NlsGge.ThirdConsultation.M016Q.laurent_core u R F hrep.2 hval hG N φ hφ ψ hψ
    ⟨C, J, hC, fun j hj => by
      obtain ⟨hch, -, -, hb⟩ := h031 j hj
      exact ⟨hch, hb⟩⟩
    (fun k hk hkN => WKB_hierarchy_coefficients_complex (N + 2) ψ k hk hkN)

end NlsGge.ThirdConsultation.M
