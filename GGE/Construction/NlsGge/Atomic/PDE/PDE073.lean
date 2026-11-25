import Mathlib
import NlsGge.ThirdConsultation.PDE.ActualGibbs
import NlsGge.ThirdConsultation.PDE.PDE073Sup

                                                                                                  
                                                                                                                           
                                                                                                                             
                                                                                                                        
                                                                                                                        
                       
set_option autoImplicit false
open Set Filter Topology Metric MeasureTheory
open scoped BigOperators ENNReal InnerProductSpace
open NlsGge.Pilot NlsGge.Sobolev38 NlsGge.Birkhoff
open NlsGge.SpectralFoundations NlsGge.GK38 NlsGge.Atomic.Common
open NlsGge.GKDefinitionDesign NlsGge.NLS38
open NlsGge.ThirdConsultation.Common
namespace NlsGge.ThirdConsultation.PDE

theorem actual_finite_density_twist
    (lower upper : ℝ) (c : ℕ → ℝ)
    (hlower : 0 < lower) (hbound : ∀ j : ℕ, lower ≤ c j)
    (hupper : ∀ j : ℕ, c j ≤ upper)
    (Lambda : Finset ℤ) (t : ℝ) (z : Lambda → ℂ) :
  finiteGibbsDensity c Lambda
    (NlsGge.NLS38.twist (NlsGge.Birkhoff.kappaΛ38 actualOmega Lambda t) z) =
      finiteGibbsDensity c Lambda z := by
  unfold finiteGibbsDensity NlsGge.Birkhoff.nuHatDens38
  rw [PDE073Aux.actual_densΛ38_twist]

end NlsGge.ThirdConsultation.PDE
